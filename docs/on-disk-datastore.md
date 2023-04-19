# On-Disk Store

The VM uses an on-disk store to manage state persistence. The structure of this
store will be explained in the following document, together with how session
commitments affect the state.

### Genesis Commit

Assume that we create a VM with a root directory path "/tmp/piecrust". We then
proceed to start a "genesis session", and deploy two modules with identifiers
`module_1` and `module_2`. After committing this session - with root `root_1`
and, the directory will contain the following files:

```
/tmp/piecrust/
    root_1/
        bytecode/ # Module bytecodes
            module_1
            module_2
        memory/   # Module memories
            module_1
            module_2
        index    # Module memory hashes
```

### Another Commit

When can then start a new session using `Root1` as a base commit, and make some
modifications to the state by performing transactions. Let's say that we made
some modifications to `module_1`'s memory, and deploy a new module with
identifier `module_3`. We can then commit to those changes forming a new commit
with `root_2`.

The directory will then look like this:

```
/tmp/piecrust/
    root_1/
        bytecode/
            module_1
            module_2
        memory/
            module_1
            module_2
        index
    root_2/
        bytecode/
            module_1 # Hard link
            module_2 # Hard link
            module_3 # New module
        memory/
            module_1 # Hard link
            module_1.diff # Delta
            module_2 # Hard link
            module_3
        index
```

To save space on disk, the `module_1.diff` file is a compressed delta between
the contents of the memory on disk and what they would be in `root_2`. Coupled
together with the hard linking of memories and bytecodes, this allows us to
effectively maintain a commit history and allow for independent commit
deletions, while maintaining a small file system footprint.

### Yet Another Commit...

We start yet another session, this time basing ourselves from `root_2`, and we make
some changes to `module_2`. The

When we commit yet another session, make some change additional commit files are created:

```
/tmp/piecrust/
    root_1/*
    root_2/
        bytecode/
            module_1
            module_2
            module_3
        memory/
            module_1
            module_1.diff
            module_2
            module_3
        index
    root_3/
        bytecode/
            module_1
            module_2
            module_3
        memory/
            module_1
            module_1.diff # Hard link
            module_2
            module_2.diff
            module_3
        index
```

### Index File

The `index` file in all commit directories contains a map of all existing
modules to their respective memory hashes. This is handy for avoiding IO
operations when computing the root of the state.

### Copy-on-write and Session concurrency 

Copy-on-write memory mapped files - see [mmap](https://man7.org/linux/man-pages/man2/mmap.2.html) -
can be leveraged to make commits read-only, while keeping changes in memory.
Consequently, combined with the fact that commits are independent, sessions can
be run concurrently, as long as they're synchronized with commit deletions - since
deleting a commit while a session is "using it" would cause data corruption.

### Glossary

- **Commit** - state after a session
- **Genesis Session** - a session without a commit preceding it
- **Memory** - a module's WASM linear memory
- **Module** - the pair of WASM bytecode and memory
- **Root** - the merkle root of all memories in the state
- **State** - a collection of modules
- **Session** - a series of modifications to a commit
- **VM** - the `π-crust` virtual machine
