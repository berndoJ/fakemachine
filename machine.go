//go:build linux && (arm64 || amd64)

package fakemachine

import (
	"al.essio.dev/pkg/shellescape"
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"text/template"

	writerhelper "github.com/go-debos/fakemachine/cpio"
)

func mergedUsrSystem() (bool, error) {
	f, err := os.Lstat("/bin")
	if err != nil {
		return false, fmt.Errorf("failed to stat '/bin': %w", err)
	}

	return (f.Mode() & os.ModeSymlink) == os.ModeSymlink, nil
}

// Parse modinfo output and return the value of module attributes
// There may be multiple row with same fieldname so []string
// is used to return all data.
func getModData(modpath string, fieldname string) ([]string, error) {
	out, err := exec.Command("modinfo", modpath).Output()
	if err != nil {
		return nil, fmt.Errorf("failed to call modinfo for module %q: %w", modpath, err)
	}

	var fieldValue []string
	scanner := bufio.NewScanner(strings.NewReader(string(out)))
	scanner.Split(bufio.ScanLines)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		name, value, ok := strings.Cut(line, ":")
		if !ok {
			return nil, fmt.Errorf("unexpected modinfo output for module %q: %q", modpath, line)
		}
		if strings.TrimSpace(name) == fieldname {
			fieldValue = append(fieldValue, strings.TrimSpace(value))
		}
	}
	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("failed to scan modinfo output for module %q: %w", modpath, err)
	}
	return fieldValue, nil
}

// Normalizes a module name similar to modinfo's `module_normalize()` function.
// See: https://github.com/kmod-project/kmod/blob/master/shared/util.c
func normalizeModuleName(modname string) string {
	// Replace all '-' with '_' and stop at first '.'
	var b strings.Builder
	for _, r := range modname {
		switch r {
		case '-':
			b.WriteRune('_')
		case '.':
			return b.String()
		default:
			b.WriteRune(r)
		}
	}
	return b.String()
}

// Given a path to a kernel module, extract the module's name by trimming the
// directory and standard .ko suffixes.
func moduleNameFromPath(modpath string) string {
	base := filepath.Base(modpath)

	suffixes := []string {
		".ko", ".ko.gz", ".ko.xz", ".ko.zst",
	}

	for _, suffix := range suffixes {
		if strings.HasSuffix(base, suffix) {
			return strings.TrimSuffix(base, suffix)
		}
	}

	return base
}

// Scan either a modules.builtin or modules.dep file for the path to a module
// given by it's name. If depFormat is true, then the file is expected to be
// in the format of a modules.dep file, otherwise one path per line.
// Returns the path to the module, whether the module was found, and any error.
func scanModPathFile(filename string, modname string, depFormat bool) (string, bool, error) {
	file, err := os.Open(filename)
	if err != nil {
		// If the file doesn't exist, return no error, since e.g. modules.builtin
		// might not exist on all systems.
		if errors.Is(err, os.ErrNotExist) {
			return "", false, nil
		}
		return "", false, fmt.Errorf("failed to open file %s: %w", filename, err)
	}
	defer file.Close()

	want := normalizeModuleName(modname)

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}

		modPath := line

		// In *.dep files, the path is followed by a colon.
		if depFormat {
			beforeColon, _, found := strings.Cut(modPath, ":")
			if !found {
				continue
			}
			modPath = strings.TrimSpace(beforeColon)
		}

		got := normalizeModuleName(moduleNameFromPath(modPath))
		if got == want {
			// Found the module we're looking for.
			return modPath, true, nil
		}
	}

	if err := scanner.Err(); err != nil {
		return "", false, err
	}

	return "", false, nil
}

// Get the path to a kernel module file by it's name in a given module directory.
func getModPath(modname string, moduleDir string) (string, bool, error) {
	// Check loadable modules from modules.dep
	path, found, err := scanModPathFile(filepath.Join(moduleDir, "modules.dep"), modname, true)
	if err != nil {
		return "", false, err
	} else if found {
		return filepath.Join(moduleDir, path), false, nil
	}

	// Check builtin modules from modules.builtin.
	path, found, err = scanModPathFile(filepath.Join(moduleDir, "modules.builtin"), modname, false)
	if err != nil {
		return "", false, err
	} else if found {
		return filepath.Join(moduleDir, path), true, nil
	}

	return "", false, fmt.Errorf("module %q not found in %s", modname, moduleDir)
}

// Get all dependent module
func getModDepends(modname string, moddir string) ([]string, error) {
	modpath, isBuiltin, err := getModPath(modname, moddir)
	if err != nil {
		return nil, err
	} else if isBuiltin {
		// Builtin modules don't have dependencies, since the dependencies are
		// compiled into the kernel itself.
		return nil, nil
	}
	
	deplist, err := getModData(modpath, "depends")
	if err != nil {
		return nil, err
	}
	var modlist []string
	for _, v := range deplist {
		if v != "" {
			modlist = append(modlist, strings.Split(v, ",")...)
		}
	}

	// Busybox expects a full dependency list for each module rather than just
	// direct dependencies, so recurse the module dependency tree:
	// https://github.com/mirror/busybox/blob/1dd2685dcc735496d7adde87ac60b9434ed4a04c/modutils/modprobe.c#L46-L49
	var sublist []string
	for _, mod := range modlist {
		deps, err := getModDepends(mod, moddir)
		if err != nil {
			return nil, fmt.Errorf("get dependencies for module %q: %w", mod, err)
		}
		sublist = append(sublist, deps...)
	}

	modlist = append(modlist, sublist...)

	return modlist, nil
}

var suffixes = map[string]writerhelper.Transformer{
	".ko":     NullDecompressor,
	".ko.gz":  GzipDecompressor,
	".ko.xz":  XzDecompressor,
	".ko.zst": ZstdDecompressor,
}

func (m *Machine) copyModules(w *writerhelper.WriterHelper, tgt_moddir string, modname string, copiedModules map[string]bool) error {
	moddir, err := m.backend.ModulePath()
	if err != nil {
		return fmt.Errorf("failed to get module path from backend: %w", err)
	}
	modpath, isBuiltin, err := getModPath(modname, moddir)
	if err != nil {
		return fmt.Errorf("kernel module %q not found in module directory %q: %w", modname, moddir, err)
	}

	if isBuiltin || copiedModules[modname] {
		return nil
	}

	found := false
	for suffix, fn := range suffixes {
		if strings.HasSuffix(modpath, suffix) {
			if _, err := os.Stat(modpath); err != nil {
				return fmt.Errorf("failed to stat module file %q: %w", modpath, err)
			}

			// Get the relative path of the module to the source module directory,
			// and construct a destination path with the target moddir.
			relPath, err := filepath.Rel(moddir, modpath)
			if err != nil {
				return fmt.Errorf("failed to get relative path for module %q: %w", modpath, err)
			}
			dest := filepath.Join(tgt_moddir, relPath)

			// The suffix is the complete thing - ".ko.foobar"
			// Reinstate the required ".ko" part, after trimming.
			dest = strings.TrimSuffix(dest, suffix) + ".ko"

			if err := w.TransformFileTo(modpath, dest, fn); err != nil {
				return fmt.Errorf("failed to transform module file %q: %w", modpath, err)
			}
			found = true
			break
		}
	}
	if !found {
		return errors.New("kernel module extension/suffix unknown")
	}

	copiedModules[modname] = true

	deplist, err := getModDepends(modname, moddir)
	if err != nil {
		return fmt.Errorf("failed to get dependencies for kernel module %q: %w", modname, err)
	}
	for _, mod := range deplist {
		if err := m.copyModules(w, tgt_moddir, mod, copiedModules); err != nil {
			return err
		}
	}

	return nil
}

// Evaluate any symbolic link, then return the path's directory. Returns an
// absolute path. Think of it as realpath(1) + dirname(1) in bash.
func realDir(path string) (string, error) {
	var p string
	var err error
	if p, err = filepath.Abs(path); err != nil {
		return "", fmt.Errorf("failed to get absolute path for %s: %w", path, err)
	}
	if p, err = filepath.EvalSymlinks(p); err != nil {
		return "", fmt.Errorf("failed to evaluate symlinks for %s: %w", p, err)
	}
	return filepath.Dir(p), nil
}

// addVolumeIfExists adds volumePath as a machine volume if it exists on the host.
//
// It returns true if the volume was added. A missing path is not treated as an
// error and returns false, nil. If the path exists but is not a directory, or
// cannot be checked, it returns false and an error.
func (m *Machine) addVolumeIfExists(volumePath string) (bool, error) {
	stat, err := os.Stat(volumePath)

	if err != nil {
		if errors.Is(err, os.ErrNotExist) {
			return false, nil
		}

		return false, fmt.Errorf("failed to check %q: %w", volumePath, err)
	}

	if !stat.IsDir() {
		return false, fmt.Errorf("failed to add volume %q: not a directory", volumePath)
	}

	m.AddVolume(volumePath)
	return true, nil
}

func (m *Machine) addVolumesWithGlob(pattern string) error {
	matches, err := filepath.Glob(pattern)
	if err != nil {
		return fmt.Errorf("glob %s: %w", pattern, err)
	}

	for _, volumePath := range matches {
		if _, err := m.addVolumeIfExists(volumePath); err != nil {
			return err
		}
	}

	return nil
}

type Arch string

const (
	Amd64 Arch = "amd64"
	Arm64 Arch = "arm64"
)

var archMap = map[string]Arch{
	"amd64": Amd64,
	"arm64": Arm64,
}

var archDynamicLinker = map[Arch]string{
	Amd64: "/lib64/ld-linux-x86-64.so.2",
	Arm64: "/lib/ld-linux-aarch64.so.1",
}

type mountPoint struct {
	hostDirectory    string
	machineDirectory string
	label            string
	static           bool
}

type image struct {
	path  string
	label string
}

type Machine struct {
	arch       Arch
	backend    backend
	mounts     []mountPoint
	count      int
	images     []image
	memory     int
	numcpus    int
	sectorSize int
	showBoot   bool
	quiet      bool
	mergedUsr  bool
	Environ    []string

	scratchsize int64
	scratchpath string
	scratchfile string
	scratchdev  string
	initrdpath  string

	busyboxPath *string
}

// Create a new machine object with the auto backend
func NewMachine() (*Machine, error) {
	return NewMachineWithBackend("auto")
}

// Create a new machine object
func NewMachineWithBackend(backendName string) (*Machine, error) {
	var err error
	m := &Machine{memory: 2048, numcpus: runtime.NumCPU(), sectorSize: 512}

	var ok bool
	if m.arch, ok = archMap[runtime.GOARCH]; !ok {
		return nil, fmt.Errorf("unsupported arch %s", runtime.GOARCH)
	}

	m.backend, err = newBackend(backendName, m)
	if err != nil {
		return nil, err
	}

	// usr is mounted by specific label via /init
	m.addStaticVolume("/usr", "usr")

	// check if the host is a merged-usr system
	m.mergedUsr, err = mergedUsrSystem()
	if err != nil {
		return nil, fmt.Errorf("failed to check if the host is a merged-usr system: %w", err)
	}

	if !m.mergedUsr {
		m.addStaticVolume("/sbin", "sbin")
		m.addStaticVolume("/bin", "bin")
		m.addStaticVolume("/lib", "lib")
	}

	// Mounts for ssl certificates
	if _, err := m.addVolumeIfExists("/etc/ca-certificates"); err != nil {
		return nil, err
	}
	if _, err := m.addVolumeIfExists("/etc/ssl"); err != nil {
		return nil, err
	}

	// Mounts for java VM configuration, especially security policies
	if err := m.addVolumesWithGlob("/etc/java*"); err != nil {
		return nil, err
	}

	// Dbus configuration
	if _, err := m.addVolumeIfExists("/etc/dbus-1"); err != nil {
		return nil, err
	}

	// Debian alternative symlinks
	if _, err := m.addVolumeIfExists("/etc/alternatives"); err != nil {
		return nil, err
	}

	// Debian binfmt registry
	if _, err := m.addVolumeIfExists("/var/lib/binfmts"); err != nil {
		return nil, err
	}

	return m, nil
}

func InMachine() (ret bool) {
	_, ret = os.LookupEnv("IN_FAKE_MACHINE")

	return
}

// Check whether the auto backend is supported
func Supported() bool {
	_, err := newBackend("auto", nil)
	return err == nil
}

const initScript = `#!/bin/busybox sh

busybox mount -t proc proc /proc
busybox mount -t sysfs none /sys

# probe additional modules
{{ range $m := .Backend.InitModules }}
busybox modprobe {{ $m }}
{{ end }}

# mount static volumes
{{ range $point := StaticVolumes .Machine }}
{{ MountVolume $.Backend $point }}
{{ end }}

exec /lib/systemd/systemd
`
const networkdTemplate = `
[Match]
Type=ether

[Network]
DHCP=ipv4
# Disable link-local address to speedup boot
LinkLocalAddressing=no
IPv6AcceptRA=no
`

const networkdLinkTemplate = `
[Match]
Type=ether

[Link]
# Give the interface a static name
Name=ethernet0
`

const commandWrapper = `#!/bin/sh
/lib/systemd/systemd-networkd-wait-online -q --interface=ethernet0
if [ $? != 0 ]; then
  echo "WARNING: Network setup failed"
  echo "== Journal =="
  journalctl -a --no-pager
  echo "== networkd =="
  networkctl status
  networkctl list
  echo 1 > /run/fakemachine/result
  exit
fi

%[1]s
echo $? > /run/fakemachine/result
`

// The line 'Environment=%[2]s' is used for environment variables optionally
// configured using Machine.SetEnviron()
const serviceTemplate = `
[Unit]
Description=fakemachine runner
Conflicts=shutdown.target
Before=shutdown.target
Requires=basic.target
Wants=systemd-resolved.service binfmt-support.service systemd-networkd.service
After=basic.target systemd-resolved.service binfmt-support.service systemd-networkd.service
OnFailure=poweroff.target

[Service]
Environment=HOME=/root IN_FAKE_MACHINE=yes %[2]s
WorkingDirectory=-/scratch
ExecStart=/wrapper
ExecStopPost=/bin/sync
ExecStopPost=/bin/systemctl poweroff -q -ff
Type=idle
TTYPath=%[1]s
StandardInput=tty-force
StandardOutput=inherit
StandardError=inherit
KillMode=process
IgnoreSIGPIPE=no
SendSIGHUP=yes
LimitNOFILE=4096
`

// helper function to generate a mount command for a given mountpoint
func tmplMountVolume(b backend, m mountPoint) string {
	fsType, options := b.MountParameters(m)

	mntCommand := []string{"busybox", "mount", "-v"}
	mntCommand = append(mntCommand, "-t", fsType)
	if len(options) > 0 {
		mntCommand = append(mntCommand, "-o", strings.Join(options, ","))
	}
	mntCommand = append(mntCommand, m.label)
	mntCommand = append(mntCommand, m.machineDirectory)
	return strings.Join(mntCommand, " ")
}

// helper function to return the static volumes from a machine, since the mounts variable is unexported
// include the extra static mounts from the backend
func tmplStaticVolumes(m Machine) []mountPoint {
	mounts := []mountPoint{}
	for _, mount := range append(m.mounts, m.backend.InitStaticVolumes()...) {
		if mount.static {
			mounts = append(mounts, mount)
		}
	}
	return mounts
}

func executeInitScriptTemplate(m *Machine, b backend) ([]byte, error) {
	helperFuncs := template.FuncMap{
		"MountVolume":   tmplMountVolume,
		"StaticVolumes": tmplStaticVolumes,
	}

	type templateVars struct {
		Machine *Machine
		Backend backend
	}
	tmplVariables := templateVars{m, b}

	tmpl := template.Must(template.New("init").Funcs(helperFuncs).Parse(initScript))
	out := &bytes.Buffer{}
	if err := tmpl.Execute(out, tmplVariables); err != nil {
		return nil, fmt.Errorf("failed to execute init script template: %w", err)
	}
	return out.Bytes(), nil
}

func (m *Machine) addStaticVolume(directory, label string) {
	m.mounts = append(m.mounts, mountPoint{directory, directory, label, true})
}

// AddVolumeAt mounts hostDirectory from the host at machineDirectory in the
// fake machine
func (m *Machine) AddVolumeAt(hostDirectory, machineDirectory string) {
	label := fmt.Sprintf("virtfs-%d", m.count)
	for _, mount := range m.mounts {
		if mount.hostDirectory == hostDirectory && mount.machineDirectory == machineDirectory {
			// Do not need to add already existing mount
			return
		}
	}
	m.mounts = append(m.mounts, mountPoint{hostDirectory, machineDirectory, label, false})
	m.count = m.count + 1
}

// AddVolume mounts directory from the host at the same location in the
// fake machine
func (m *Machine) AddVolume(directory string) {
	m.AddVolumeAt(directory, directory)
}

// CreateImageWithLabel creates an image file at path a given size and exposes
// it in the fake machine using the given label as the serial id. If size is -1
// then the image should already exist and the size isn't modified.
//
// label needs to be less then 20 characters due to limitations from qemu
//
// The returned string is the device path of the new image as seen inside
// fakemachine.
func (m *Machine) CreateImageWithLabel(path string, size int64, label string) (_ string, err error) {
	if len(label) >= 20 {
		return "", fmt.Errorf("image label %q too long; cannot be more than 20 characters", label)
	}

	for _, image := range m.images {
		if image.label == label {
			return "", fmt.Errorf("image with label %q already exists", label)
		}
	}

	flags := os.O_WRONLY
	if size >= 0 {
		flags |= os.O_CREATE
	}

	i, err := os.OpenFile(path, flags, 0666)
	if err != nil {
		if size < 0 {
			return "", fmt.Errorf("failed to open existing image file %s: %w", path, err)
		}
		return "", fmt.Errorf("failed to create image file %s: %w", path, err)
	}
	defer func() {
		if closeErr := i.Close(); closeErr != nil {
			err = errors.Join(err, fmt.Errorf("failed to close image file %s: %w", path, closeErr))
		}
	}()

	if size >= 0 {
		if err := i.Truncate(size); err != nil {
			return "", fmt.Errorf("failed to truncate image file %s: %w", path, err)
		}
	}

	m.images = append(m.images, image{path, label})

	return fmt.Sprintf("/dev/disk/by-fakemachine-label/%s", label), nil
}

// CreateImage does the same as CreateImageWithLabel but lets the library pick
// the label.
func (m *Machine) CreateImage(imagepath string, size int64) (string, error) {
	label := fmt.Sprintf("fakedisk-%d", len(m.images))

	return m.CreateImageWithLabel(imagepath, size, label)
}

// diskSuffix returns the disk name suffix for the i-th disk (0-indexed),
// following Linux device naming: a, b, ..., z, aa, ab, ..., az, ba, ...
func diskSuffix(i int) string {
	suffix := ""
	for ; i >= 0; i = (i/26 - 1) {
		suffix = string(rune('a'+i%26)) + suffix
	}
	return suffix
}

// SetMemory sets the fakemachines amount of memory (in megabytes). Defaults to
// 2048 MB
func (m *Machine) SetMemory(memory int) {
	m.memory = memory
}

// SetNumCPUs sets the number of CPUs exposed to the fakemachine. Defaults to
// the number of available cores in the system.
func (m *Machine) SetNumCPUs(numcpus int) {
	m.numcpus = numcpus
}

// SetSectorSize overrides the default sector size(512 bytes) for the image
// exposed to the fakemachine
func (m *Machine) SetSectorSize(sectorSize int) {
	m.sectorSize = sectorSize
}

// SetShowBoot sets whether to show boot/console messages from the fakemachine.
func (m *Machine) SetShowBoot(showBoot bool) {
	m.showBoot = showBoot
}

// SetQuiet sets whether fakemachine should print additional information (e.g.
// the command to be ran) or just print the stdout/stderr of the command to be
// ran.
func (m *Machine) SetQuiet(quiet bool) {
	m.quiet = quiet
}

// SetScratch sets the size and location of on-disk scratch space to allocate
// (sparsely) for /scratch. If not set /scratch will be backed by memory. If
// Path is "" then the working directory is used as a default storage location
func (m *Machine) SetScratch(scratchsize int64, path string) {
	m.scratchsize = scratchsize
	m.scratchpath = path
}

// SetBackendOption sets a backend-specific option, identified by it's key and
// the given string value. The supported options depend on the backend used,
// an error is returned in case the option is invalid.
func (m *Machine) SetBackendOption(key string, value string) error {
	if m.backend == nil {
		return fmt.Errorf("backend not set")
	}
	return m.backend.SetOption(key, value)
}

// SetBackendOptions sets multiple backend-specific options; see SetBackendOption.
func (m *Machine) SetBackendOptions(options map[string]string) error {
	for key, value := range options {
		if err := m.SetBackendOption(key, value); err != nil {
			return err
		}
	}
	return nil
}

// Set an optional path to a busybox binary to be used in the initrd. If not set,
// busybox will be looked for in the host's PATH.
func (m *Machine) SetBusyboxPath(path string) error {
	if _, err := os.Stat(path); err != nil {
		return fmt.Errorf("failed to stat busybox binary at %q: %w", path, err)
	}
	
	m.busyboxPath = &path
	return nil
}

func (m Machine) generateFstab(w *writerhelper.WriterHelper, backend backend) error {
	fstab := []string{"# Generated fstab file by fakemachine"}

	if m.scratchfile == "" {
		fstab = append(fstab, "none /scratch tmpfs size=95% 0 0")
	} else {
		fstab = append(fstab, fmt.Sprintf("%s /scratch ext4 defaults,relatime 0 0",
			m.scratchdev))
	}

	for _, point := range m.mounts {
		fstype, options := backend.MountParameters(point)
		fstab = append(fstab,
			fmt.Sprintf("%s %s %s %s 0 0",
				point.label, point.machineDirectory, fstype, strings.Join(options, ",")))
	}
	fstab = append(fstab, "")

	err := w.WriteFile("/etc/fstab", strings.Join(fstab, "\n"), 0755)
	if err != nil {
		return fmt.Errorf("failed to write fstab: %w", err)
	}
	return nil
}

func stripCompressionSuffix(module string) (string, error) {
	for suffix := range suffixes {
		// The suffix is the complete thing - ".ko.foobar"
		// Reinstate the required ".ko" part, after trimming.
		if trimmed, ok := strings.CutSuffix(module, suffix); ok {
			return trimmed + ".ko", nil
		}
	}
	return "", errors.New("module extension/suffix unknown")
}

func (m *Machine) generateModulesDep(w *writerhelper.WriterHelper, tgt_moddir string, moddir string, modules map[string]bool) error {
	output := make([]string, len(modules))
	moddir, err := m.backend.ModulePath()
	if err != nil {
		return fmt.Errorf("failed to get module path from backend: %w", err)
	}
	i := 0
	for mod := range modules {
		modpath, isBuiltin, err := getModPath(mod, moddir)
		if err != nil {
			return fmt.Errorf("failed to get path for module %q: %w", mod, err)
		} else if isBuiltin {
			// Builtin modules aren't of interest for modules.dep.
			continue
		}
		modpath, err = filepath.Rel(moddir, modpath)
		if err != nil {
			return fmt.Errorf("failed to get relative path for module %q: %w", mod, err)
		}
		modpath, err = stripCompressionSuffix(path.Join(tgt_moddir, modpath))
		if err != nil {
			return fmt.Errorf("failed to strip compression suffix for module %q: %w", mod, err)
		}
		deplist, err := getModDepends(mod, moddir)
		if err != nil {
			return fmt.Errorf("failed to get dependencies for module %q: %w", mod, err)
		}
		deps := make([]string, len(deplist))
		for j, dep := range deplist {
			deppath, isBuiltin, err := getModPath(dep, moddir)
			if err != nil {
				return fmt.Errorf("failed to get path for dependency %q of module %q: %w", dep, mod, err)
			} else if isBuiltin {
				// Builtin modules aren't of interest for modules.dep.
				continue
			}
			deppath, err = filepath.Rel(moddir, deppath)
			if err != nil {
				return fmt.Errorf("failed to get relative path for dependency %q of module %q: %w", dep, mod, err)
			}
			deppath, err = stripCompressionSuffix(path.Join(tgt_moddir, deppath))
			if err != nil {
				return fmt.Errorf("failed to strip compression suffix for dependency %q of module %q: %w", dep, mod, err)
			}
			deps[j] = deppath
		}
		output[i] = fmt.Sprintf("%s: %s", modpath, strings.Join(deps, " "))
		i++
	}

	path := path.Join(tgt_moddir, "modules.dep")
	if err := w.WriteFile(path, strings.Join(output, "\n"), 0644); err != nil {
		return fmt.Errorf("failed to write modules.dep: %w", err)
	}
	return nil
}

func (m *Machine) SetEnviron(environ []string) {
	m.Environ = environ
}

func (m *Machine) writerKernelModules(w *writerhelper.WriterHelper, moddir string, modules []string) error {
	if len(modules) == 0 {
		return nil
	}
	
	// Since the user can set a custom module directory via the backend options,
	// we cannot rely on this directory being in the desired
	// /usr/lib/modules/$(uname -r) or /lib/modules/$(uname -r) format. Thus,
	// we construct a static target dir for the initrd from the kernel release.
	// We keep the original behavior with the /usr prefix for merged-usr systems.
	kernel_release, err := m.backend.KernelRelease()
	if err != nil {
		return fmt.Errorf("failed to get kernel release from backend: %w", err)
	}
	tgt_moddir := "/lib/modules/" + kernel_release
	if m.mergedUsr {
		tgt_moddir = "/usr" + tgt_moddir
	}

	modfiles := []string{
		"modules.builtin",
		"modules.alias",
		"modules.symbols"}

	for _, v := range modfiles {
		if err := w.CopyFileTo(moddir + "/" + v, tgt_moddir + "/" + v); err != nil {
			return fmt.Errorf("failed to copy kernel module file %s: %w", moddir+"/"+v, err)
		}
	}

	copiedModules := make(map[string]bool)

	for _, modname := range modules {
		if err := m.copyModules(w, tgt_moddir, modname, copiedModules); err != nil {
			return err
		}
	}

	return m.generateModulesDep(w, tgt_moddir, moddir, copiedModules)
}

func (m *Machine) setupscratch() error {
	if m.scratchsize == 0 {
		return nil
	}

	if m.scratchpath == "" {
		cwd, err := os.Getwd()
		if err != nil {
			return fmt.Errorf("failed to get working directory for scratch path: %w", err)
		}
		m.scratchpath = cwd
	}

	tmpfile, err := os.CreateTemp(m.scratchpath, "fake-scratch.img.")
	if err != nil {
		return fmt.Errorf("failed to create temp file for scratch: %w", err)
	}
	m.scratchfile = tmpfile.Name()
	if err := tmpfile.Close(); err != nil {
		return fmt.Errorf("failed to close scratch temp file: %w", err)
	}

	m.scratchdev, err = m.CreateImageWithLabel(m.scratchfile, m.scratchsize, "fake-scratch")
	if err != nil {
		return err
	}
	mkfs := exec.Command("mkfs.ext4", "-q", m.scratchfile)
	err = mkfs.Run()
	if err != nil {
		return fmt.Errorf("failed to format scratch disk: %w", err)
	}

	return nil
}

func (m *Machine) cleanup() error {
	if m.scratchfile == "" {
		return nil
	}

	if err := os.Remove(m.scratchfile); err != nil {
		return fmt.Errorf("failed to remove scratchfile %q: %w", m.scratchfile, err)
	}

	m.scratchfile = ""
	return nil
}

func (m *Machine) buildInitrd(command string, extracontent [][2]string) (err error) {
	f, err := os.OpenFile(m.initrdpath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0755)
	if err != nil {
		return fmt.Errorf("failed to create initrd file: %w", err)
	}

	defer func() {
		if closeErr := f.Close(); closeErr != nil {
			err = errors.Join(err, fmt.Errorf("failed to close initrd file: %w", closeErr))
		}
	}()

	kernelModuleDir, err := m.backend.ModulePath()
	if err != nil {
		return fmt.Errorf("failed to get kernel module directory: %w", err)
	}

	w := writerhelper.NewWriterHelper(f)
	defer func() {
		if closeErr := w.Close(); closeErr != nil {
			err = errors.Join(err, fmt.Errorf("failed to close cpio writer: %w", closeErr))
		}
	}()

	err = w.WriteDirectories([]writerhelper.WriteDirectory{
		{Directory: "/scratch", Perm: 01777},
		{Directory: "/var/tmp", Perm: 01777},
		{Directory: "/var/lib/dbus", Perm: 0755},
		{Directory: "/tmp", Perm: 01777},
		{Directory: "/sys", Perm: 0755},
		{Directory: "/proc", Perm: 0755},
		{Directory: "/run", Perm: 0755},
		{Directory: "/usr", Perm: 0755},
		{Directory: "/usr/bin", Perm: 0755},
		{Directory: "/lib64", Perm: 0755},
	})
	if err != nil {
		return fmt.Errorf("failed to write directories: %w", err)
	}

	err = w.WriteSymlink("/run", "/var/run", 0755)
	if err != nil {
		return fmt.Errorf("failed to write /var/run symlink: %w", err)
	}

	if m.mergedUsr {
		err = w.WriteSymlinks([]writerhelper.WriteSymlink{
			{Target: "/usr/sbin", Link: "/sbin", Perm: 0755},
			{Target: "/usr/bin", Link: "/bin", Perm: 0755},
			{Target: "/usr/lib", Link: "/lib", Perm: 0755},
			{Target: "/usr/lib64", Link: "/lib64", Perm: 0755},
		})
		if err != nil {
			return fmt.Errorf("failed to write merged-usr symlinks: %w", err)
		}
	} else {
		err = w.WriteDirectories([]writerhelper.WriteDirectory{
			{Directory: "/sbin", Perm: 0744},
			{Directory: "/bin", Perm: 0755},
			{Directory: "/lib", Perm: 0755},
		})
		if err != nil {
			return fmt.Errorf("failed to write non-merged-usr directories: %w", err)
		}
	}

	prefix := ""
	if m.mergedUsr {
		prefix = "/usr"
	}

	var busyboxPath string
	if m.busyboxPath != nil {
		// Use the user-provided busybox path
		busyboxPath = *m.busyboxPath
	} else {
		// search for busybox; in some distros it's located under /sbin
		var err error
		busyboxPath, err = exec.LookPath("busybox")
		if err != nil {
			return fmt.Errorf("failed to find busybox: %w", err)
		}
	}
	err = w.CopyFileTo(busyboxPath, prefix+"/bin/busybox")
	if err != nil {
		return fmt.Errorf("failed to copy busybox: %w", err)
	}

	/* Ensure systemd-resolved is available */
	if _, err := os.Stat("/lib/systemd/systemd-resolved"); err != nil {
		return fmt.Errorf("systemd-resolved not found: %w", err)
	}

	dynamicLinker := archDynamicLinker[m.arch]
	err = w.CopyFile(prefix + dynamicLinker)
	if err != nil {
		return fmt.Errorf("failed to copy dynamic linker: %w", err)
	}

	/* C libraries */
	libraryDir, err := realDir(dynamicLinker)
	if err != nil {
		return err
	}
	err = w.CopyFile(libraryDir + "/libc.so.6")
	if err != nil {
		return fmt.Errorf("failed to copy libc.so.6: %w", err)
	}
	err = w.CopyFile(libraryDir + "/libresolv.so.2")
	if err != nil {
		return fmt.Errorf("failed to copy libresolv.so.2: %w", err)
	}

	err = w.WriteCharDevice("/dev/console", 5, 1, 0700)
	if err != nil {
		return fmt.Errorf("failed to write /dev/console device: %w", err)
	}

	// Linker configuration
	err = w.CopyFile("/etc/ld.so.conf")
	if err != nil {
		return fmt.Errorf("failed to copy ld.so.conf: %w", err)
	}

	err = w.CopyTree("/etc/ld.so.conf.d")
	if err != nil {
		return fmt.Errorf("failed to copy ld.so.conf.d: %w", err)
	}

	// Core system configuration
	err = w.WriteFile("/etc/machine-id", "", 0444)
	if err != nil {
		return fmt.Errorf("failed to write machine-id: %w", err)
	}

	err = w.WriteFile("/etc/hostname", "fakemachine", 0444)
	if err != nil {
		return fmt.Errorf("failed to write hostname: %w", err)
	}

	err = w.CopyFile("/etc/passwd")
	if err != nil {
		return fmt.Errorf("failed to copy passwd: %w", err)
	}

	err = w.CopyFile("/etc/group")
	if err != nil {
		return fmt.Errorf("failed to copy group: %w", err)
	}

	err = w.CopyFile("/etc/nsswitch.conf")
	if err != nil {
		return fmt.Errorf("failed to copy nsswitch.conf: %w", err)
	}

	// udev rules
	udevRules := strings.Join(m.backend.UdevRules(), "\n") + "\n"
	err = w.WriteFile("/etc/udev/rules.d/61-fakemachine.rules", udevRules, 0444)
	if err != nil {
		return fmt.Errorf("failed to write udev rules: %w", err)
	}

	err = w.WriteFile("/etc/systemd/network/ethernet.network",
		networkdTemplate, 0444)
	if err != nil {
		return fmt.Errorf("failed to write ethernet.network: %w", err)
	}

	err = w.WriteFile("/etc/systemd/network/10-ethernet.link",
		networkdLinkTemplate, 0444)
	if err != nil {
		return fmt.Errorf("failed to write ethernet.link: %w", err)
	}

	err = w.WriteSymlink(
		"/lib/systemd/resolv.conf",
		"/etc/resolv.conf",
		0755)
	if err != nil {
		return fmt.Errorf("failed to write resolv.conf symlink: %w", err)
	}

	err = m.writerKernelModules(w, kernelModuleDir, m.backend.InitModules())
	if err != nil {
		return fmt.Errorf("failed to write kernel modules: %w", err)
	}

	err = w.WriteFile("etc/systemd/system/fakemachine.service",
		fmt.Sprintf(serviceTemplate, m.backend.JobOutputTTY(), strings.Join(m.Environ, " ")), 0644)
	if err != nil {
		return fmt.Errorf("failed to write fakemachine.service: %w", err)
	}

	err = w.WriteSymlink(
		"/lib/systemd/system/serial-getty@ttyS0.service",
		"/dev/null",
		0755)
	if err != nil {
		return fmt.Errorf("failed to write serial-getty symlink: %w", err)
	}

	err = w.WriteFile("/wrapper",
		fmt.Sprintf(commandWrapper, command), 0755)
	if err != nil {
		return fmt.Errorf("failed to write wrapper script: %w", err)
	}

	init, err := executeInitScriptTemplate(m, m.backend)
	if err != nil {
		return err
	}

	err = w.WriteFileRaw("/init", init, 0755)
	if err != nil {
		return fmt.Errorf("failed to write init script: %w", err)
	}

	err = m.generateFstab(w, m.backend)
	if err != nil {
		return fmt.Errorf("failed to generate fstab: %w", err)
	}

	for _, v := range extracontent {
		err = w.CopyFileTo(v[0], v[1])
		if err != nil {
			return fmt.Errorf("failed to copy extra content %s: %w", v[0], err)
		}
	}

	return nil
}

// Start the machine running the given command and adding the extra content to
// the cpio. Extracontent is a list of {source, dest} tuples
func (m *Machine) startup(command string, extracontent [][2]string) (code int, err error) {
	defer func() {
		if cleanupErr := m.cleanup(); cleanupErr != nil {
			err = errors.Join(err, fmt.Errorf("cleanup failed: %w", cleanupErr))
		}
	}()

	if err := os.Setenv("PATH", os.Getenv("PATH")+":/sbin:/usr/sbin"); err != nil {
		return -1, fmt.Errorf("failed to set PATH: %w", err)
	}

	/* Sanity check mountpoints */
	for _, v := range m.mounts {
		/* Check the directory exists on the host */
		stat, err := os.Stat(v.hostDirectory)
		if err != nil {
			return -1, fmt.Errorf("couldn't stat %s: %w", v.hostDirectory, err)
		}
		if !stat.IsDir() {
			return -1, fmt.Errorf("couldn't mount %s inside machine: expected a directory", v.hostDirectory)
		}

		/* Check for whitespace in the machine directory */
		if regexp.MustCompile(`\s`).MatchString(v.machineDirectory) {
			return -1, fmt.Errorf("couldn't mount %s inside machine: machine directory (%s) contains whitespace", v.hostDirectory, v.machineDirectory)
		}

		/* Check for whitespace in the label */
		if regexp.MustCompile(`\s`).MatchString(v.label) {
			return -1, fmt.Errorf("couldn't mount %s inside machine: label (%s) contains whitespace", v.hostDirectory, v.label)
		}
	}

	tmpdir, err := os.MkdirTemp("", "fakemachine-")
	if err != nil {
		return -1, fmt.Errorf("failed to create temp directory: %w", err)
	}
	m.AddVolumeAt(tmpdir, "/run/fakemachine")
	defer func() {
		if removeErr := os.RemoveAll(tmpdir); removeErr != nil {
			err = errors.Join(err, fmt.Errorf("failed to remove tempdir %s: %w", tmpdir, removeErr))
		}
	}()

	err = m.setupscratch()
	if err != nil {
		return -1, err
	}

	m.initrdpath = path.Join(tmpdir, "initramfs.cpio")
	if err := m.buildInitrd(command, extracontent); err != nil {
		return -1, err
	}

	if !m.quiet {
		fmt.Printf("Running %s using %s backend\n", command, m.backend.Name())
	}

	// Set a default result of failure so that if the backend fails to start
	// we get a defined exit code instead of an error reading the result file.
	resultPath := path.Join(tmpdir, "result")
	if err := os.WriteFile(resultPath, []byte("1"), 0644); err != nil {
		return -1, fmt.Errorf("failed to create result file: %w", err)
	}

	success, err := m.backend.Start()
	if err != nil {
		return -1, fmt.Errorf("error starting %s backend: %w", m.backend.Name(), err)
	}
	if !success {
		return -1, fmt.Errorf("error starting %s backend: unknown error", m.backend.Name())
	}

	result, err := os.Open(resultPath)
	if err != nil {
		return -1, fmt.Errorf("failed to open result file: %w", err)
	}
	defer func() {
		if closeErr := result.Close(); closeErr != nil {
			err = errors.Join(err, fmt.Errorf("failed to close result file: %w", closeErr))
		}
	}()

	exitstr, err := io.ReadAll(result)
	if err != nil {
		return -1, fmt.Errorf("failed to read result file: %w", err)
	}
	exitcode, err := strconv.Atoi(strings.TrimSpace(string(exitstr)))

	if err != nil {
		return -1, fmt.Errorf("failed to parse exit code: %w", err)
	}

	return exitcode, nil
}

// Run creates the machine running the given command
func (m *Machine) Run(command string) (int, error) {
	return m.startup(command, nil)
}

// RunInMachineWithArgs runs the caller binary inside the fakemachine with the
// specified commandline arguments
func (m *Machine) RunInMachineWithArgs(args []string) (int, error) {
	name := path.Join("/", path.Base(os.Args[0]))

	quotedArgs := shellescape.QuoteCommand(args)
	command := strings.Join([]string{name, quotedArgs}, " ")

	executable, err := exec.LookPath(os.Args[0])

	fmt.Printf("Executable path: %s\n", executable)
	fmt.Printf("Name: %s\n", name)

	if err != nil {
		return -1, fmt.Errorf("failed to find executable: %w", err)
	}

	return m.startup(command, [][2]string{{executable, name}})
}

// RunInMachine runs the caller binary inside the fakemachine with the same
// commandline arguments as the parent
func (m *Machine) RunInMachine() (int, error) {
	return m.RunInMachineWithArgs(os.Args[1:])
}
