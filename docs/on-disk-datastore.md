# On-Disk Store

The VM uses an on-disk store to manage state persistence. The structure of this
store will be explained in the following document, together with how session
commitments affect the state.

### Genesis Commit

Assume that we create a VM with a root directory path "/tmp/piecrust". We then
proceed to start a "genesis session", and deploy two contracts with identifiers
`contract_1` and `contract_2`. After committing this session - with root `root_1`
and, the directory will contain the following files:

```
/tmp/piecrust/
    root_1/
        bytecode/ # Contract bytecodes
            contract_1
            contract_2
        memory/   # Contract memories
            contract_1/
                00000000 # Memory pages
                00010000
                00020000
            contract_2/
                00000000
                00010000
        index    # Contract memory hashes
```

### Another Commit

We can then start a new session using `root_1` as a base commit, and make some
modifications to the state by performing transactions. Let's say that we made
some modifications to `contract_1`'s first memory page, and deploy a new
contract with identifier `contract_3`. We can then commit to those changes
forming a new commit with `root_2`.

The directory will then look like this:

```
/tmp/piecrust/
    root_1/
        bytecode/
            contract_1
            contract_2
        memory/
            contract_1/
                00000000
                00010000
                00020000
            contract_2/
                00000000
                00010000
        index
    root_2/
        bytecode/
            contract_1 # Hard link
            contract_2 # Hard link
            contract_3 # New contract
        memory/
            contract_1/
                00000000 # New file (modified)
                00010000 # Hard link (unmodified)
                00020000 # Hard link
            contract_2/
                00000000 # Hard link
                00010000 # Hard link
            contract_3/
                00000000 # New file (new contract)
        index
```

Only modified memory pages are saved to disk, and the rest are hard linked from
the previous commit. Together, these two measures allow us to both save space on
disk and maintain a history of independent commits.

### Index File

The `index` file in all commit directories contains a map of all existing
contracts to their respective memory hashes. This is handy for avoiding IO
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
- **Memory** - a contract's WASM linear memory
- **Contract** - the pair of WASM bytecode and memory
- **Root** - the merkle root of all memories in the state
- **State** - a collection of contracts
- **Session** - a series of modifications to a commit
- **VM** - the `π-crust` virtual machine
