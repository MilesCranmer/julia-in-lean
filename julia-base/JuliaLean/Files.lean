import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Files.Model
import JuliaLean.Files.Props
import JuliaLean.Files.Proven
import JuliaLean.Files.Refuted
import JuliaLean.Files.Coverage

namespace JuliaLean.Files

open JuliaLean.Registry
open JuliaLean.Files.Coverage

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "files-mkpath-postcondition", juliaFile := "base/file.jl"
    juliaFns := ["mkpath"]
    statement := "For every relative, absolute, trailing-slash, symlink, or empty path state, mkpath preserves the path spelling, creates every missing component, accepts existing directory components, and errors at a file component."
    source := "base/file.jl:197-203 (mkpath docstring), 239-256", status := .proven
    prop := ``MkpathPostcondition, thm := some ``mkpathPostcondition_proven },
  { id := "files-rm-flags", juliaFile := "base/file.jl"
    juliaFns := ["rm(::AbstractString; force, recursive)"]
    statement := "force suppresses exactly the missing-path error; recursive removes a nonempty directory; files and symbolic links are unlinked without traversing their targets."
    source := "base/file.jl:263-267 (rm docstring), 283-326", status := .proven
    prop := ``RmFlagsSpec, thm := some ``rmFlagsSpec_proven },
  { id := "files-rm-recursive-symlink-slash", juliaFile := "base/file.jl"
    juliaFns := ["rm(::AbstractString; recursive=true)"]
    statement := "Recursive removal of a path naming a symbolic link does not delete entries from the link target, including when the path has a trailing slash."
    source := "base/file.jl:263-267 (rm docstring)", status := .refuted
    prop := ``RmSymlinkSafe, thm := some ``rmSymlinkSafe_refuted
    issue := "none found (queries: rm symlink trailing slash, rm recursive symlink, rm symlink directory contents)"
    notes := "rm(\"link/\"; recursive=true) deletes the target child, then throws ENOTDIR and leaves the link and target directory. Same on 1.13.2 and master." },
  { id := "files-cp-force-dangling-symlink", juliaFile := "base/file.jl"
    juliaFns := ["cp(::AbstractString, ::AbstractString; force=true)", "checkfor_mv_cp_cptree", "sendfile"]
    statement := "cp(src, dst; force=true) removes every existing destination before creating the copy at dst and never writes through a destination symlink."
    source := "base/file.jl:423-434 (cp docstring)", status := .refuted
    prop := ``CpForceReplaces, thm := some ``cpForceReplaces_refuted
    issue := "none found (queries: cp dangling symlink, force symlink destination, cp force symlink)"
    notes := "For a dangling dst symlink, ispath(dst) is false: cp leaves the link and creates its missing target. Same on 1.13.2 and master." },
  { id := "files-mv-force", juliaFile := "base/file.jl"
    juliaFns := ["mv(::AbstractString, ::AbstractString; force)", "_mv_replace", "_mv_noreplace"]
    statement := "For distinct source and destination paths, force=true replaces every destination; force=false succeeds exactly when the destination is absent."
    source := "base/file.jl:461-465 (mv docstring), 505-558", status := .proven
    prop := ``MvForceSpec, thm := some ``mvForceSpec_proven },
  { id := "files-tempname-contract", juliaFile := "base/file.jl"
    juliaFns := ["tempname", "_tempname", "_rand_filename"]
    statement := "For every parent path shape and candidate stream, tempname rejects a non-directory parent, skips candidates whose targets exist through max_tries, constructs the jl_ prefix and requested suffix, creates nothing, and records cleanup as requested."
    source := "base/file.jl:778-804, 845-878 (tempname docstring)", status := .proven
    prop := ``TempnameContract, thm := some ``tempnameContract_proven },
  { id := "files-tempname-dangling-symlink", juliaFile := "base/file.jl"
    juliaFns := ["tempname", "_tempname"]
    statement := "The path returned by tempname differs from every filesystem entry that exists at call time, including a dangling symbolic link."
    source := "base/file.jl:848-852 (tempname docstring)", status := .refuted
    prop := ``TempnameUnused, thm := some ``tempnameUnused_refuted
    issue := "none found (queries: tempname dangling symlink, tempname existing symlink, _tempname ispath)"
    notes := "With the filename RNG reset around an existing dangling symlink candidate, tempname returns that symlink path. Same on 1.13.2 and master." },
  { id := "files-mktemp-contract", juliaFile := "base/file.jl"
    juliaFns := ["mktemp", "mktemp(::Function, parent)"]
    statement := "mktemp atomically creates and opens a jl_-prefixed file in every usable parent, records cleanup exactly when requested, and its function overload removes the file on every exit."
    source := "base/file.jl:825-840, 882-892, 944-967", status := .proven
    prop := ``MktempContract, thm := some ``mktempContract_proven },
  { id := "files-mktempdir-contract", juliaFile := "base/file.jl"
    juliaFns := ["mktempdir", "mktempdir(::Function, parent)"]
    statement := "mktempdir creates a directory with the requested prefix and a random suffix in every usable parent, records cleanup exactly when requested, and its function overload removes the whole directory on every exit."
    source := "base/file.jl:896-941, 969-998", status := .proven
    prop := ``MktempdirContract, thm := some ``mktempdirContract_proven },
  { id := "files-readdir-options", juliaFile := "base/file.jl"
    juliaFns := ["readdir", "_readdir"]
    statement := "readdir returns every scanned name once; sort=true orders the names, sort=false preserves scan order, and join=true applies joinpath(dir, name) to every result."
    source := "base/file.jl:1005-1019 (readdir docstring), 1176-1207", status := .proven
    prop := ``ReaddirOptions, thm := some ``readdirOptions_proven },
  { id := "files-walkdir-order", juliaFile := "base/file.jl"
    juliaFns := ["walkdir", "_walkdir"]
    statement := "walkdir yields every directory exactly once in sorted sibling order: preorder for topdown=true and postorder for topdown=false; non-followed symlinks occur once in files."
    source := "base/file.jl:1355-1364 (walkdir docstring), 1403-1443", status := .proven
    prop := ``WalkdirOrder, thm := some ``walkdirOrder_proven },
  { id := "files-touch-postcondition", juliaFile := "base/file.jl"
    juliaFns := ["touch(::AbstractString)", "touch(::Filesystem.File)"]
    statement := "touch creates a missing empty file, preserves existing contents, sets the modification time to now, and returns its input path or file."
    source := "base/file.jl:561-569 (touch docstring), 586-594; base/filesystem.jl:450-459", status := .proven
    prop := ``TouchPostcondition, thm := some ``touchPostcondition_proven },
  { id := "files-chmod-recursive", juliaFile := "base/file.jl"
    juliaFns := ["chmod(::AbstractString, ::Integer; recursive)"]
    statement := "Recursive chmod changes the root and every non-link descendant to mode and leaves symbolic links untouched; nonrecursive chmod changes only the root."
    source := "base/file.jl:1622-1646", status := .proven
    prop := ``ChmodRecursive, thm := some ``chmodRecursive_proven },
  { id := "files-stat-mode-layout", juliaFile := "base/stat.jl"
    juliaFns := ["filemode", "isdir", "islink", "ispath", "uperm", "gperm", "operm", "filesize"]
    statement := "For all 2^16 POSIX modes, isdir and islink decode bits 12-15, owner/group/other permissions decode their three-bit fields, filemode returns mode, ispath tests ioerrno, and filesize returns size."
    source := "base/stat.jl:59-105, 300-338, 364-566", status := .proven
    prop := ``StatModeLayout, thm := some ``statModeLayout_proven },
  { id := "files-file-offsets", juliaFile := "base/filesystem.jl"
    juliaFns := ["unsafe_write(::Filesystem.File)", "read(::Filesystem.File)", "readbytes!", "seek", "position", "bytesavailable"]
    statement := "Current-offset writes advance by their length, explicit-offset writes preserve position, reads advance by bytes returned, seek sets the requested offset, and bytesavailable is max(filesize-position, 0)."
    source := "base/filesystem.jl:324-445", status := .proven
    prop := ``FileOffsetSpec, thm := some ``fileOffsetSpec_proven },
  { id := "files-coverage-cwd-mode", juliaFile := "base/file.jl"
    juliaFns := ["pwd", "cd", "checkmode", "mkdir"]
    statement := "Working-directory buffer retries, temporary-directory restoration order, mode validation, and mkdir result handling follow the source branches."
    source := "base/file.jl:54-194", status := .proven
    prop := ``CwdModeBehavior, thm := some ``cwdModeBehavior },
  { id := "files-coverage-tree-copy", juliaFile := "base/file.jl"
    juliaFns := ["_resolved_path", "_is_within", "checkfor_mv_cp_cptree", "cptree", "_cptree", "cp"]
    statement := "Resolved-path selection, containment checks, and recursive copying preserve files and un-followed links while following requested link targets in child order."
    source := "base/file.jl:348-458", status := .proven
    prop := ``TreeCopyBehavior, thm := some ``treeCopyBehavior },
  { id := "files-coverage-temp-runtime", juliaFile := "base/file.jl"
    juliaFns := ["tempdir", "prepare_for_deletion", "temp_cleanup_later", "temp_cleanup_forget", "temp_cleanup_purge_prelocked", "temp_cleanup_purge_all", "temp_cleanup_postprocess", "temp_cleanup_atexit", "__postinit__", "_rand_filename", "tempname", "_tempname", "mktemp", "mktempdir"]
    statement := "Temporary-path probing, permission preparation, cleanup registration and purging, random slugs, and callback cleanup preserve the source update and event order."
    source := "base/file.jl:605-998", status := .proven
    prop := ``TempRuntimeBehavior, thm := some ``tempRuntimeBehavior },
  { id := "files-coverage-direntry-iterator", juliaFile := "base/file.jl"
    juliaFns := ["DirEntry accessors and predicates", "readdir", "_readdir", "DirEntryIterator", "_eachentry_open!", "close(::DirEntryIterator)", "iterate(::DirEntryIterator)", "eachentry", "walkdir", "_walkdir"]
    statement := "Directory-entry ordering and type fallback, joined-name rendering, lazy iterator open and close state, and yielded entry construction follow the source branches."
    source := "base/file.jl:1000-1443", status := .proven
    prop := ``DirEntryIteratorBehavior, thm := some ``dirEntryIteratorBehavior },
  { id := "files-coverage-primitives", juliaFile := "base/file.jl"
    juliaFns := ["unlink", "rename", "sendfile", "hardlink", "symlink", "readlink", "chmod", "chown", "DiskStat accessors", "diskstat"]
    statement := "Primitive filesystem wrappers propagate negative return codes, copy and symlink flags follow keywords and platform selection, and DiskStat fields project exactly."
    source := "base/file.jl:1445-1713", status := .proven
    prop := ``PrimitiveFileBehavior, thm := some ``primitiveFileBehavior },
  { id := "files-coverage-stat-construction", juliaFile := "base/stat.jl"
    juliaFns := ["StatStruct equality, hash, and constructors", "checkstat", "stat_call", "stat", "lstat"]
    statement := "Stat equality and hashing omit desc, failed stat construction zeros decoded fields, accepted errno values return a record, and other errno values raise the I/O error path."
    source := "base/stat.jl:59-251", status := .proven
    prop := ``StatConstructionBehavior, thm := some ``statConstructionBehavior },
  { id := "files-coverage-stat-display-mode", juliaFile := "base/stat.jl"
    juliaFns := ["iso_datetime_with_relative", "getusername", "getgroupname", "show_statstruct", "show(::StatStruct)", "filemode_string", "mode predicates"]
    statement := "Relative-time units, optional user and group names, stat display fields, ten-character mode strings, file types, and special mode bits follow the source order."
    source := "base/stat.jl:110-182,255-566", status := .proven
    prop := ``StatDisplayModeBehavior, thm := some ``statDisplayModeBehavior },
  { id := "files-coverage-stat-path", juliaFile := "base/stat.jl"
    juliaFns := ["path stat accessors", "islink(path...)", "samefile", "ismount"]
    statement := "Path accessors project the selected stat field, samefile requires existing equal device and inode pairs, and mount detection uses the directory, link, device, and root-inode checks in order."
    source := "base/stat.jl:568-625", status := .proven
    prop := ``StatPathBehavior, thm := some ``statPathBehavior },
  { id := "files-coverage-file-lifecycle-transfer", juliaFile := "base/filesystem.jl"
    juliaFns := ["uv_fs_req_cleanup", "File", "rawhandle", "setup_stdio", "open", "isopen", "check_open", "close", "trylockfile", "unlockfile", "closewrite", "sendfile", "unsafe_write", "write", "truncate", "futime"]
    statement := "Filesystem.File lifecycle, lock results, sendfile chunk offsets, write forwarding, truncation, and timestamp updates preserve the source checks and state changes."
    source := "base/filesystem.jl:155-354", status := .proven
    prop := ``FileLifecycleTransferBehavior, thm := some ``fileLifecycleTransferBehavior },
  { id := "files-coverage-file-read-access", juliaFile := "base/filesystem.jl"
    juliaFns := ["read(::File)", "unsafe_read", "bytesavailable", "eof", "readbytes!", "readavailable", "seek", "seekend", "skip", "position", "fd", "stat(::File)", "touch(::File)", "isexecutable", "isreadable", "iswritable"]
    statement := "File reads and wrappers, end and relative seeks, bytes-available and EOF calculations, descriptor projections, touch, and access checks follow the source arithmetic and return-code tests."
    source := "base/filesystem.jl:356-539", status := .proven
    prop := ``FileReadAccessBehavior, thm := some ``fileReadAccessBehavior },
  { id := "files-coverage-path-primitives", juliaFile := "base/path.jl"
    juliaFns := ["isseparator", "splitdrive", "homedir", "isabspath", "pathsep", "realpath", "abstract-string path wrappers"]
    statement := "POSIX separator and drive rules, user-home retry results, realpath error forwarding, and abstract-string wrappers follow their source branches."
    source := "base/path.jl:27-30,184-223,371,663-679,781-808,962", status := .proven
    prop := ``PathPrimitiveBehavior, thm := some ``pathPrimitiveBehavior },
  { id := "files-coverage-path-user", juliaFile := "base/path.jl"
    juliaFns := ["homedir(username)", "contractuser", "expanduser"]
    statement := "POSIX user lookup retries and contractuser prefix scanning stop at missing prefixes and choose current or owning-user homes in source order."
    source := "base/path.jl:781-908", status := .proven
    prop := ``PathUserBehavior, thm := some ``pathUserBehavior },
  { id := "files-coverage-path-uri", juliaFile := "base/path.jl"
    juliaFns := ["encode_uri_component", "uripath"]
    statement := "URI path encoding preserves RFC3986 unreserved bytes plus slash, percent-encodes other bytes with uppercase hexadecimal, and constructs the POSIX file URI in source order."
    source := "base/path.jl:965-1030", status := .proven
    prop := ``PathUriBehavior, thm := some ``pathUriBehavior },
  { id := "files-method-filesystem-lifecycle", juliaFile := "base/filesystem.jl"
    juliaFns := ["uv_fs_req_cleanup", "File constructors", "rawhandle", "setup_stdio", "open", "isopen", "check_open", "close"]
    statement := "Each Filesystem.File lifecycle method performs its own source-ordered allocation, syscall, state update, cleanup, and error check for every input and syscall result."
    source := "base/filesystem.jl:155-216", status := .proven
    prop := ``FileLifecycleMethods, thm := some ``fileLifecycleMethods },
  { id := "files-method-filesystem-locks", juliaFile := "base/filesystem.jl"
    juliaFns := ["trylockfile", "unlockfile", "closewrite"]
    statement := "File lock methods check openness, distinguish acquired, unavailable, and error results, and closewrite returns nothing for every file."
    source := "base/filesystem.jl:268-306", status := .proven
    prop := ``FileLockMethods, thm := some ``fileLockMethods },
  { id := "files-method-filesystem-writes", juliaFile := "base/filesystem.jl"
    juliaFns := ["sendfile", "unsafe_write", "write(::File, ::UInt8)", "truncate", "futime"]
    statement := "File transfer and mutation methods mirror their exact openness checks, chunk loop, syscall arguments, request cleanup, return values, and error branches."
    source := "base/filesystem.jl:309-354", status := .proven
    prop := ``FileWriteMethods, thm := some ``fileWriteMethods },
  { id := "files-method-filesystem-scalar-reads", juliaFile := "base/filesystem.jl"
    juliaFns := ["read(::File, ::Type{UInt8})", "read(::File, ::Type{Char})", "read(::File, ::Type{<:AbstractChar})", "unsafe_read"]
    statement := "Scalar and unsafe File reads mirror openness, syscall errors, EOF checks, UTF-8 continuation consumption, and exact-length enforcement for every input."
    source := "base/filesystem.jl:356-398", status := .proven
    prop := ``FileScalarReadMethods, thm := some ``fileScalarReadMethods },
  { id := "files-method-filesystem-bulk-reads", juliaFile := "base/filesystem.jl"
    juliaFns := ["bytesavailable", "eof", "readbytes!", "read(::File)", "readavailable", "read(::File, nb)"]
    statement := "Bulk File read methods mirror available-byte arithmetic, resize conditions, requested counts, and wrapper delegation for all file states and sizes."
    source := "base/filesystem.jl:400-416", status := .proven
    prop := ``FileBulkReadMethods, thm := some ``fileBulkReadMethods },
  { id := "files-method-filesystem-seek-descriptors", juliaFile := "base/filesystem.jl"
    juliaFns := ["seek", "seekend", "skip", "position", "fd", "stat(::File)", "touch(::File)"]
    statement := "File seek and descriptor methods mirror their exact lseek modes, returned-position checks, projections, stat delegation, and platform touch result handling."
    source := "base/filesystem.jl:422-459", status := .proven
    prop := ``FileSeekDescriptorMethods, thm := some ``fileSeekDescriptorMethods },
  { id := "files-method-filesystem-access", juliaFile := "base/filesystem.jl"
    juliaFns := ["isexecutable", "isreadable", "iswritable"]
    statement := "Each access predicate calls the source access mode, compares the return code with zero, and each AbstractString overload performs only String conversion and delegation."
    source := "base/filesystem.jl:479-539", status := .proven
    prop := ``FileAccessMethods, thm := some ``fileAccessMethods },
  { id := "files-method-stat-values", juliaFile := "base/stat.jl"
    juliaFns := ["StatStruct equality", "StatStruct hash", "StatStruct constructors"]
    statement := "StatStruct equality and hash use every field except desc, the empty constructor uses zero fields plus ENOENT, and buffer constructors zero decoded fields exactly when ioerrno is nonzero."
    source := "base/stat.jl:76-108", status := .proven
    prop := ``StatValueMethods, thm := some ``statValueMethods },
  { id := "files-method-stat-display", juliaFile := "base/stat.jl"
    juliaFns := ["iso_datetime_with_relative", "getusername", "getgroupname", "show_statstruct", "show(::StatStruct)"]
    statement := "Stat display methods choose the first nonzero relative-time unit, omit missing or empty account names, select error or data fields, and forward compact versus text display exactly."
    source := "base/stat.jl:110-182", status := .proven
    prop := ``StatDisplayMethods, thm := some ``statDisplayMethods },
  { id := "files-method-stat-calls", juliaFile := "base/stat.jl"
    juliaFns := ["checkstat", "stat_call", "stat", "lstat"]
    statement := "Each stat and lstat method mirrors its buffer allocation, zeroing, selected syscall, StatStruct decoding, accepted error check, conversion wrapper, and vararg join delegation."
    source := "base/stat.jl:186-251", status := .proven
    prop := ``StatCallMethods, thm := some ``statCallMethods },
  { id := "files-method-stat-fields", juliaFile := "base/stat.jl"
    juliaFns := ["filemode", "filemode_string", "filesize", "mtime", "ctime", "StatStruct type and permission predicates"]
    statement := "Every direct StatStruct accessor and predicate mirrors its exact field projection, POSIX mask, permission shift, and mode-string table for every mode."
    source := "base/stat.jl:310-566", status := .proven
    prop := ``StatFieldMethods, thm := some ``statFieldMethods },
  { id := "files-method-stat-paths", juliaFile := "base/stat.jl"
    juliaFns := ["ispath(path)", "generated stat accessors", "islink(path)", "samefile", "ismount"]
    statement := "Path stat methods mirror allowed access errors, String conversion, stat versus lstat selection, accessor dispatch, existing device and inode checks, and mount-point branch order."
    source := "base/stat.jl:376-385,568-625", status := .proven
    prop := ``StatPathMethods, thm := some ``statPathMethods },
  { id := "files-method-path-core", juliaFile := "base/path.jl"
    juliaFns := ["isseparator(::Char)", "isseparator(::UInt8)", "splitdrive(::String)", "isabspath(::String)", "pathsep", "assertstring"]
    statement := "Each POSIX core path method mirrors its own literal separator, empty-drive result, first-character absolute test, separator constant, or string type check for every input."
    source := "base/path.jl:27-30,200-223,371,416,466", status := .proven
    prop := ``PathCoreMethods, thm := some ``pathCoreMethods },
  { id := "files-method-path-homedir", juliaFile := "base/path.jl"
    juliaFns := ["homedir()"]
    statement := "homedir retries UV_ENOBUFS with the required buffer size, returns the successful path, and propagates other libuv errors for every reply sequence."
    source := "base/path.jl:184-198", status := .proven
    prop := ``PathHomedirMethod, thm := some ``pathHomedirMethod },
  { id := "files-method-path-realpath", juliaFile := "base/path.jl"
    juliaFns := ["realpath"]
    statement := "realpath allocates its request, calls uv_fs_realpath, cleans the request on both branches, returns the resolved path on success, and frees the request."
    source := "base/path.jl:663-679", status := .proven
    prop := ``PathRealpathMethod, thm := some ``pathRealpathMethod },
  { id := "files-method-path-abstract-wrappers", juliaFile := "base/path.jl"
    juliaFns := ["generated AbstractString path wrappers"]
    statement := "Each generated AbstractString wrapper converts to String and delegates to its corresponding POSIX path method, including cwd-sensitive abspath."
    source := "base/path.jl:961-963", status := .proven
    prop := ``PathAbstractWrapperMethod, thm := some ``pathAbstractWrapperMethod },
  { id := "files-method-path-users", juliaFile := "base/path.jl"
    juliaFns := ["homedir(username)", "contractuser", "contractuser(::AbstractString)"]
    statement := "POSIX user-home lookup retries ERANGE and resolves the returned uid, while contractuser scans existing prefixes and chooses current or owning-user homes in source order."
    source := "base/path.jl:781-850,908", status := .proven
    prop := ``PathUserMethods, thm := some ``pathUserMethods },
  { id := "files-method-path-uri", juliaFile := "base/path.jl"
    juliaFns := ["encode_uri_component", "uripath(::String)", "uripath(::AbstractString)"]
    statement := "URI methods preserve allowed bytes, emit uppercase percent escapes, normalize and split the absolute local path, select WSL or hostname, and delegate AbstractString conversion."
    source := "base/path.jl:965-1030", status := .proven
    prop := ``PathUriMethods, thm := some ``pathUriMethods },
  { id := "files-method-pwd", juliaFile := "base/file.jl"
    juliaFns := ["pwd"]
    statement := "pwd retries UV_ENOBUFS, resizes to the requested capacity, returns the successful cwd bytes, and propagates every other libuv error."
    source := "base/file.jl:54-68", status := .proven
    prop := ``PwdMethod, thm := some ``pwdMethod_proven },
  { id := "files-method-cd", juliaFile := "base/file.jl"
    juliaFns := ["cd(dir)", "cd()", "cd(f, dir)", "cd(f)"]
    statement := "Each active POSIX cd overload performs its exact homedir or chdir delegation, and callback cd saves, changes, calls, restores, and closes in finally order."
    source := "base/file.jl:91-96,109-119,149", status := .proven
    prop := ``CdMethods, thm := some ``cdMethods },
  { id := "files-method-checkmode", juliaFile := "base/file.jl"
    juliaFns := ["checkmode"]
    statement := "checkmode returns every integer in 0:0o777 and raises ArgumentError for every integer outside that interval."
    source := "base/file.jl:151-156", status := .proven
    prop := ``CheckmodeMethod, thm := some ``checkmodeMethod },
  { id := "files-method-mkdir", juliaFile := "base/file.jl"
    juliaFns := ["mkdir"]
    statement := "mkdir validates mode before its libuv call, cleans the request on success and error, returns path on success, and propagates a negative return as I/O error."
    source := "base/file.jl:179-194", status := .proven
    prop := ``MkdirMethod, thm := some ``mkdirMethod },
  { id := "files-method-resolved-path", juliaFile := "base/file.jl"
    juliaFns := ["_resolved_path"]
    statement := "_resolved_path makes relative paths absolute, returns realpath for existing targets unless preserving a final link, stops at a self parent, and reconstructs missing tails in source order."
    source := "base/file.jl:348-357", status := .proven
    prop := ``ResolvedPathMethod, thm := some ``resolvedPathMethod },
  { id := "files-method-is-within", juliaFile := "base/file.jl"
    juliaFns := ["_is_within"]
    statement := "_is_within returns true exactly for equal paths or a component-boundary-prefixed inner path."
    source := "base/file.jl:359-360", status := .proven
    prop := ``IsWithinMethod, thm := some ``isWithinMethod },
  { id := "files-method-check-copy", juliaFile := "base/file.jl"
    juliaFns := ["checkfor_mv_cp_cptree"]
    statement := "The copy and move guard performs source-containment, destination existence, force, same-file, reverse-containment, and removal decisions in the exact source order."
    source := "base/file.jl:363-391", status := .proven
    prop := ``CheckCopyMethod, thm := some ``checkCopyMethod_proven },
  { id := "files-method-cptree", juliaFile := "base/file.jl"
    juliaFns := ["cptree(::String)", "_cptree", "cptree(::AbstractString)"]
    statement := "cptree rejects non-directories, runs the overlap guard, creates the destination, recursively copies entries in scan order with the requested symlink policy, and the AbstractString wrapper converts and delegates."
    source := "base/file.jl:393-420", status := .proven
    prop := ``CptreeMethods, thm := some ``cptreeMethods },
  { id := "files-method-cp", juliaFile := "base/file.jl"
    juliaFns := ["cp"]
    statement := "cp runs its destination guard first, then preserves an un-followed source link, recursively copies a directory, or copies a file, and returns the destination."
    source := "base/file.jl:447-458", status := .proven
    prop := ``CpMethod, thm := some ``cpMethod_proven },
  { id := "files-method-delayed-delete-ref", juliaFile := "base/file.jl"
    juliaFns := ["delayed_delete_ref"]
    statement := "delayed_delete_ref joins tempdir with the fixed julia_delayed_deletes_ref component for every temporary directory."
    source := "base/file.jl:260", status := .proven
    prop := ``DelayedDeleteRefMethod, thm := some ``delayedDeleteRefMethod_proven },
  { id := "files-method-tempdir", juliaFile := "base/file.jl"
    juliaFns := ["tempdir"]
    statement := "tempdir retries UV_ENOBUFS, returns the successful path, classifies missing and nondirectory paths, suppresses only I/O and system access errors, and emits the matching warning."
    source := "base/file.jl:605-632", status := .proven
    prop := ``TempdirMethod, thm := some ``tempdirMethod_proven },
  { id := "files-method-prepare-deletion", juliaFile := "base/file.jl"
    juliaFns := ["prepare_for_deletion"]
    statement := "prepare_for_deletion returns for nondirectories and otherwise adds write and execute permissions to the root and every walked child directory while suppressing only filesystem errors."
    source := "base/file.jl:643-664", status := .proven
    prop := ``PrepareForDeletionMethod, thm := some ``prepareForDeletionMethod_proven },
  { id := "files-method-cleanup-later", juliaFile := "base/file.jl"
    juliaFns := ["temp_cleanup_later"]
    statement := "temp_cleanup_later stores old-and-asap so delayed cleanup wins, purges above the threshold, doubles the observed size with its minimum, and returns nothing."
    source := "base/file.jl:671-683", status := .proven
    prop := ``CleanupLaterMethod, thm := some ``cleanupLaterMethod_proven },
  { id := "files-method-cleanup-forget", juliaFile := "base/file.jl"
    juliaFns := ["temp_cleanup_forget"]
    statement := "temp_cleanup_forget deletes the path under the cleanup lock and returns nothing for every path."
    source := "base/file.jl:685-688", status := .proven
    prop := ``CleanupForgetMethod, thm := some ``cleanupForgetMethod_proven },
  { id := "files-method-cleanup-purge", juliaFile := "base/file.jl"
    juliaFns := ["temp_cleanup_purge_prelocked"]
    statement := "The prelocked purge drops absent paths, removes force or asap paths after preparation, retains failed or still-present paths, and rethrows only interrupts."
    source := "base/file.jl:690-709", status := .proven
    prop := ``CleanupPurgePrelockedMethod, thm := some ``cleanupPurgePrelockedMethod_proven },
  { id := "files-method-cleanup-purge-all", juliaFile := "base/file.jl"
    juliaFns := ["temp_cleanup_purge_all"]
    statement := "The full purge filters absent paths, records whether GC may help, runs forced GC only then, and invokes the forced prelocked purge."
    source := "base/file.jl:711-729", status := .proven
    prop := ``CleanupPurgeAllMethod, thm := some ``cleanupPurgeAllMethod_proven },
  { id := "files-method-cleanup-postprocess", juliaFile := "base/file.jl"
    juliaFns := ["temp_cleanup_postprocess"]
    statement := "Postprocess does nothing for an empty cleanup set; otherwise it spawns the detached remover, writes paths, leaks the duplicate descriptor until exit, and closes the pipe in order."
    source := "base/file.jl:734-754", status := .proven
    prop := ``CleanupPostprocessMethod, thm := some ``cleanupPostprocessMethod_proven },
  { id := "files-method-cleanup-atexit", juliaFile := "base/file.jl"
    juliaFns := ["temp_cleanup_atexit"]
    statement := "The exit hook runs full cleanup first and then postprocesses the remaining cleanup keys under the lock."
    source := "base/file.jl:756-759", status := .proven
    prop := ``CleanupAtexitMethod, thm := some ``cleanupAtexitMethod_proven },
  { id := "files-method-file-postinit", juliaFile := "base/file.jl"
    juliaFns := ["__postinit__"]
    statement := "File post-initialization registers temp_cleanup_atexit exactly once with Base.atexit."
    source := "base/file.jl:761-763", status := .proven
    prop := ``FilePostinitMethod, thm := some ``filePostinitMethod_proven },
  { id := "files-method-rand-filename", juliaFile := "base/file.jl"
    juliaFns := ["_rand_filename"]
    statement := "_rand_filename performs exactly len libc draws and maps each modulo 62 into the fixed alphanumeric alphabet in index order."
    source := "base/file.jl:768-775", status := .proven
    prop := ``RandFilenameMethod, thm := some ``randFilenameMethod_proven },
  { id := "files-method-mktemp-unix", juliaFile := "base/file.jl"
    juliaFns := ["mktemp(parent; cleanup)"]
    statement := "POSIX mktemp constructs the jl_XXXXXX template, calls mkstemp, errors on -1, conditionally registers cleanup, and returns the modified path with an owning stream."
    source := "base/file.jl:834-840", status := .proven
    prop := ``MktempUnixMethod, thm := some ``mktempUnixMethod_proven },
  { id := "files-method-mktempdir", juliaFile := "base/file.jl"
    juliaFns := ["mktempdir(parent; prefix, cleanup)"]
    statement := "mktempdir constructs the separator-sensitive template, calls uv_fs_mkdtemp, cleans requests on both branches, conditionally registers cleanup, and returns the created path."
    source := "base/file.jl:916-941", status := .proven
    prop := ``MktempdirMethod, thm := some ``mktempdirMethod_proven },
  { id := "files-method-mktemp-callback", juliaFile := "base/file.jl"
    juliaFns := ["mktemp(::Function)"]
    statement := "Callback mktemp creates first, calls the callback, then forgets cleanup, closes the stream, removes a remaining path, and schedules failed cleanup from finally."
    source := "base/file.jl:952-967", status := .proven
    prop := ``MktempCallbackMethod, thm := some ``mktempCallbackMethod_proven },
  { id := "files-method-mktempdir-callback", juliaFile := "base/file.jl"
    juliaFns := ["mktempdir(::Function)"]
    statement := "Callback mktempdir creates first, calls the callback, then forgets cleanup, prepares and recursively removes a remaining directory, and schedules failed cleanup from finally."
    source := "base/file.jl:980-998", status := .proven
    prop := ``MktempdirCallbackMethod, thm := some ``mktempdirCallbackMethod_proven },
  { id := "files-method-direntry", juliaFile := "base/file.jl"
    juliaFns := ["DirEntry accessors", "DirEntry ordering, hash, and equality", "DirEntry type predicates", "realpath(::DirEntry)"]
    statement := "Every DirEntry method mirrors its exact field projection, joined path, reversed basename comparison, hash field order, structural equality, raw-type fallback, or realpath delegation."
    source := "base/file.jl:1122-1136", status := .proven
    prop := ``DirEntryMethods, thm := some ``dirEntryMethods },
  { id := "files-method-readdir", juliaFile := "base/file.jl"
    juliaFns := ["readdir overloads", "_readdir"]
    statement := "Every readdir overload mirrors its cwd or entry path choice, String or DirEntry output construction, join mapping, scandir order, and optional name sorting."
    source := "base/file.jl:1081-1082,1171-1207", status := .proven
    prop := ``ReaddirMethods, thm := some ``readdirMethods },
  { id := "files-method-direntry-iterator", juliaFile := "base/file.jl"
    juliaFns := ["DirEntryIterator constructor", "_eachentry_open!", "close(::DirEntryIterator)", "IteratorSize", "eltype", "isdone", "iterate"]
    statement := "Each DirEntryIterator method mirrors element-type validation, lazy open, closed-state error, atomic close, traits, end cleanup, status errors, and String or DirEntry yield construction."
    source := "base/file.jl:1235-1283", status := .proven
    prop := ``IteratorMethods, thm := some ``iteratorMethods },
  { id := "files-method-eachentry", juliaFile := "base/file.jl"
    juliaFns := ["eachentry overloads"]
    statement := "Each eachentry overload selects the exact String or DirEntry iterator, cwd or joined entry path, and the callback forms always close the iterator in finally order."
    source := "base/file.jl:1331-1351", status := .proven
    prop := ``EachentryMethods, thm := some ``eachentryMethods },
  { id := "files-method-walkdir", juliaFile := "base/file.jl"
    juliaFns := ["walkdir", "_walkdir", "tryf"]
    statement := "walkdir constructs its traversal, tryf suppresses only IOError through onerror, and _walkdir classifies entries and yields preorder or postorder in scan order."
    source := "base/file.jl:1403-1443", status := .proven
    prop := ``WalkdirMethods, thm := some ``walkdirMethods },
  { id := "files-method-unlink", juliaFile := "base/file.jl"
    juliaFns := ["unlink"]
    statement := "unlink calls jl_fs_unlink, raises the I/O path for every negative return, and returns nothing otherwise."
    source := "base/file.jl:1445-1449", status := .proven
    prop := ``UnlinkMethod, thm := some ``unlinkMethod_proven },
  { id := "files-method-rename", juliaFile := "base/file.jl"
    juliaFns := ["rename"]
    statement := "rename calls jl_fs_rename, raises the I/O path for every negative return, and returns newpath otherwise."
    source := "base/file.jl:1477-1483", status := .proven
    prop := ``RenameMethod, thm := some ``renameMethod_proven },
  { id := "files-method-sendfile-path", juliaFile := "base/file.jl"
    juliaFns := ["sendfile(::AbstractString, ::AbstractString)"]
    statement := "Path sendfile selects FICLONE alone for force and FICLONE plus EXCL otherwise, calls jl_fs_copyfile, checks its result, and returns nothing."
    source := "base/file.jl:1488-1494", status := .proven
    prop := ``SendfilePathMethod, thm := some ``sendfilePathMethod_proven },
  { id := "files-method-hardlink", juliaFile := "base/file.jl"
    juliaFns := ["hardlink"]
    statement := "hardlink calls jl_fs_hardlink, raises the I/O path for every negative return, and returns nothing otherwise."
    source := "base/file.jl:1513-1520", status := .proven
    prop := ``HardlinkMethod, thm := some ``hardlinkMethod_proven },
  { id := "files-method-symlink", juliaFile := "base/file.jl"
    juliaFns := ["symlink"]
    statement := "symlink computes its platform and target-kind flags in source order, calls jl_fs_symlink, reports every negative return, and returns nothing otherwise."
    source := "base/file.jl:1555-1596", status := .proven
    prop := ``SymlinkMethod, thm := some ``symlinkMethod_proven },
  { id := "files-method-readlink", juliaFile := "base/file.jl"
    juliaFns := ["readlink"]
    statement := "readlink allocates its request, calls uv_fs_readlink, cleans on both branches, decodes the target only on success, and always frees the request."
    source := "base/file.jl:1603-1620", status := .proven
    prop := ``ReadlinkMethod, thm := some ``readlinkMethod_proven },
  { id := "files-method-chmod", juliaFile := "base/file.jl"
    juliaFns := ["chmod"]
    statement := "chmod performs the root syscall first, stops on error, and when recursive on a directory traverses every non-link descendant with the same mode before returning path."
    source := "base/file.jl:1635-1646", status := .proven
    prop := ``ChmodMethod, thm := some ``chmodMethod_proven },
  { id := "files-method-chown", juliaFile := "base/file.jl"
    juliaFns := ["chown"]
    statement := "chown calls jl_fs_chown with path, owner, and group, raises the I/O path on a negative return, and returns path otherwise."
    source := "base/file.jl:1655-1659", status := .proven
    prop := ``ChownMethod, thm := some ``chownMethod_proven },
  { id := "files-method-diskstat", juliaFile := "base/file.jl"
    juliaFns := ["DiskStat getproperty", "DiskStat propertynames", "DiskStat show", "diskstat"]
    statement := "DiskStat methods compute byte totals and used space from their exact fields, expose the documented property order, print those three projections, and decode statfs only after a successful syscall."
    source := "base/file.jl:1680-1713", status := .proven
    prop := ``DiskstatMethods, thm := some ``diskstatMethods },
  { id := "files-method-mkpath", juliaFile := "base/file.jl"
    juliaFns := ["mkpath"]
    statement := "mkpath returns for a root or existing directory, otherwise validates mode before recursive parent creation and creates the final missing component or propagates its exact error."
    source := "base/file.jl:239-256", status := .proven
    prop := ``MkpathMethod, thm := some ``mkpathMethod_proven },
  { id := "files-method-rm", juliaFile := "base/file.jl"
    juliaFns := ["rm"]
    statement := "On POSIX, rm unlinks links and nondirectories, suppresses only forced ENOENT, recursively removes directory children when requested, and rmdirs the final directory."
    source := "base/file.jl:283-326", status := .proven
    prop := ``RmMethod, thm := some ``rmMethod_proven },
  { id := "files-method-mv", juliaFile := "base/file.jl"
    juliaFns := ["mv"]
    statement := "mv dispatches exactly to replacement or no-replacement behavior from the force keyword."
    source := "base/file.jl:505-511", status := .proven
    prop := ``MvMethods, thm := some ``mvMethods },
  { id := "files-method-mv-replace", juliaFile := "base/file.jl"
    juliaFns := ["_mv_replace"]
    statement := "_mv_replace rejects same files, tries rename first, rethrows ENOENT, removes a guarded destination after other I/O failure, retries rename, and finally copies then removes source."
    source := "base/file.jl:513-542", status := .proven
    prop := ``MvReplaceMethod, thm := some ``mvReplaceMethod_proven },
  { id := "files-method-mv-noreplace", juliaFile := "base/file.jl"
    juliaFns := ["_mv_noreplace"]
    statement := "_mv_noreplace checks destination absence first, tries rename, rethrows ENOENT, and on other I/O failure copies without force then removes source."
    source := "base/file.jl:544-558", status := .proven
    prop := ``MvNoreplaceMethod, thm := some ``mvNoreplaceMethod_proven },
  { id := "files-method-touch-path", juliaFile := "base/file.jl"
    juliaFns := ["touch(::AbstractString)"]
    statement := "Path touch opens with create and write flags, touches the file, always closes it in finally, propagates either failure, and returns path only on success."
    source := "base/file.jl:586-594", status := .proven
    prop := ``TouchPathMethod, thm := some ``touchPathMethod_proven },
  { id := "files-method-dirname-abstract", juliaFile := "base/path.jl"
    juliaFns := ["dirname(::AbstractString)"]
    statement := "The AbstractString dirname overload delegates to splitdir and returns its first component for every converted path."
    source := "base/path.jl:308", status := .proven
    prop := ``DirnameAbstractMethod, thm := some ``dirnameAbstractMethod_proven },
  { id := "files-method-basename-abstract", juliaFile := "base/path.jl"
    juliaFns := ["basename(::AbstractString)"]
    statement := "The AbstractString basename overload delegates to splitdir and returns its second component for every converted path."
    source := "base/path.jl:330", status := .proven
    prop := ``BasenameAbstractMethod, thm := some ``basenameAbstractMethod_proven },
  { id := "files-method-splitpath-abstract", juliaFile := "base/path.jl"
    juliaFns := ["splitpath(::AbstractString)"]
    statement := "The AbstractString splitpath overload converts to String and delegates to the String method for every path."
    source := "base/path.jl:393", status := .proven
    prop := ``SplitpathAbstractMethod, thm := some ``splitpathAbstractMethod_proven },
  { id := "files-method-joinpath-varargs", juliaFile := "base/path.jl"
    juliaFns := ["joinpath(::AbstractString...)"]
    statement := "The AbstractString vararg joinpath overload collects its arguments and delegates to the collection method."
    source := "base/path.jl:487", status := .proven
    prop := ``JoinpathVarargsMethod, thm := some ``joinpathVarargsMethod_proven },
  { id := "files-method-normpath-varargs", juliaFile := "base/path.jl"
    juliaFns := ["normpath(::AbstractString, ::AbstractString...)"]
    statement := "The multiargument normpath overload joins every argument first and normalizes the resulting String."
    source := "base/path.jl:595", status := .proven
    prop := ``NormpathVarargsMethod, thm := some ``normpathVarargsMethod_proven },
  { id := "files-method-abspath-varargs", juliaFile := "base/path.jl"
    juliaFns := ["abspath(::AbstractString, ::AbstractString...)"]
    statement := "The multiargument abspath overload joins every argument first and applies the cwd-sensitive String method."
    source := "base/path.jl:633", status := .proven
    prop := ``AbspathVarargsMethod, thm := some ``abspathVarargsMethod_proven },
  { id := "files-method-expanduser-abstract", juliaFile := "base/path.jl"
    juliaFns := ["expanduser(::AbstractString)"]
    statement := "The AbstractString expanduser overload converts to String and delegates to the platform String method for every path."
    source := "base/path.jl:896", status := .proven
    prop := ``ExpanduserAbstractMethod, thm := some ``expanduserAbstractMethod_proven },
  { id := "files-method-relpath-abstract", juliaFile := "base/path.jl"
    juliaFns := ["relpath(::AbstractString, ::AbstractString)"]
    statement := "The AbstractString relpath overload converts both arguments to String and delegates to the String method."
    source := "base/path.jl:958-959", status := .proven
    prop := ``RelpathAbstractMethod, thm := some ``relpathAbstractMethod_proven }
]

end JuliaLean.Files
