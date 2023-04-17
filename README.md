# Lean Seminar project: Many proofs of the Pythagoras theorem

## Installing lean

There are many ways of installing lean4, however, with mathlib4 being in the
state that it is in, we recommend using `elan`. It can be downloaded directly
from <https://github.com/leanprover/elan> (it is also available as a package
for most mainstream linux distributions).

Download lean using

```bash
elan toolchain install leanprover/lean4:nightly
```

(As of this writing, mathlib4 does not seem to be compatible with the `stable`
branch. You may also opt for one fixed nightly build, for instance,
`nightly-2023-03-17`.)

`elan` allows several versions of lean to be installed on the same system. You
can set a default lean installation using

```bash
elan default leanprover/lean4:nightly
```

Alternatively, you can create a file `lean-toolchain` in the project directory
with the line

```
leanprover/lean4:nightly
```

A nice trick to avoid having a version of lean that clashes with mathlib is to
link the mathlib `lean-toolchain` file:

```bash
ln -s lake-packages/mathlib/lean-toolchain ./
```

## Setting up the project

Authorization is needed to contribute to this project. If you are having
issues, contact Ian.

To download the project, run

```bash
git clone https://github.com/ianjauslin-rutgers/pythagoras4.git
```

or, if you prefer to use SSH,

```bash
git clone git@github.com:ianjauslin-rutgers/pythagoras4.git
```

This will download all the files in the project. However, this does not install
mathlib. To do so, `cd` to the project directory and run

```bash
lake update
```

## Cached oleans

By default, lean will compile the files it needs to compile the project. This
can be very time consuming. To make this process quicker, a pre-compiled
version of mathlib is made available by the Mathlib community.  You can
download it by running

```bash
lake exe cache get
```

However, this will only work if you are running the same version of lean as the
one that was used to compile mathlib (otherwise the oleans are unusable, and
your system will recompile all files). You can find out which nightly build of
lean was used by the latest mathlib in the file
<https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain>
You can then install that toolchain by running

```bash
elan toolchain install <mathlib_nightly>
elan default <mathlib_nightly>
```

in which you should replace `<mathlib_nightly>` with the contents of the file
<https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain>

An easier approach is to link the mathlib `lean-toolchain` file:

```bash
ln -s lake-packages/mathlib/lean-toolchain ./
```
which will ensure that your version of lean is the same as mathlib's.


## Importing André's API

To use André's API, add the following at the top of your file:

```lean
import SyntheticEuclid4
open incidence_geometry
variable [i: incidence_geometry]
```

This may take some time, as the synthetic file needs to be compiled when it is imported.

André is also working on refactoring synthetic. This process involves the creation of a lot of new API that might serve useful to the rest of the group. It might be worth checking his repo at <https://github.com/ah1112/euclid-book-I> to see if any API you need is there, and has not been ported over to Lean 4 yet. The Lean4 version of this repo is at <https://github.com/ah1112/synthetic_euclid_4> and is a dependency of this project.

## Git dos and don'ts

Git is a version control system that is very feature rich. As such, it can feel
daunting at first to learn how to use it properly, but there isn't actually
that much that you need to learn to get started.

The basic idea is that every time a change is made to a file, that change gets
recorded on the "git tree", in such a way that everyone can easily share the
latest version of the project, while keeping track of all the past versions of
the project. That way, you cannot really break anything irreversibly.

Git is also very convenient when a group of people work on the same project at
once. The basic concept to understand here is that of a "branch". A branch is a
version of the project, but, unlike a standard numbering scheme (v1.1, v1.2,
etc), git allows multiple concurrent versions to exist. For example, the
default branch is the master branch. Say Alice wants to work on Task 1, and Bob
wants to work on Task 2. Alice can create a branch, called "task1", and Bob
creates "task2". Alice works on the files on her branch, and Bob on his. That
way, both can work independently without interfering with each other, or with
the master branch. At the same time, Alice can see what Bob is doing, and vice
versa. When their work is ready to be combined, they can do so by "merging"
their branches, which will use some clever algorithms to combine Alice and
Bob's changes together. That way, Alice and Bob can work on separate things
without interference, and share their work when it is ready.

In practice, if you want to work on a task, create a branch with a name that
describes the task. For this example let's say I want to prove Proposition 1, I
will create a branch "prop1" with the following command

```bash
git checkout -b prop1
```

This creates the branch and puts you on it. You can then do your work. Every
time you complete a part of your task, you can save it to git by running

```bash
git add .
git commit
```

and writing a description of your work in the commit message. You should then
upload your changes to github with

```bash
git push
```

The first time you push after creating the branch, use

```bash
git push --set-upstream origin prop1
```

(replace "prop1" with the name of your branch).
When you are ready to merge your work with the master branch (that is, when you
are ready for your work to be included in the default branch of the project,
where it can be merged with everyone else's), create a pull request at
<https://github.com/ianjauslin-rutgers/pythagoras4/pulls>

Using git properly can help you streamline your workflow. Using it improperly
might slow you down, but it's actually quite difficult to ruin things for other
people. However, one thing you should NOT do, is rewrite git histories that
have already been pushed to the server. This makes a mess for everyone. So,
unless you know what you are doing, don't use the `git rebase` or
`git filter-branch` commands. And don't use `git commit --amend` if you have
already pushed your commit.

A great resource for learning more is <https://git-scm.com/book/en/v2>.

## VSCode/VSCodium Lean snippets

Snippets allow you to autogenerate the context for predefined commands and tab
through the variable parts. In order to use the snippets, open the Command
Palette in VSC (`Ctrl+Shift+P`), type `Snippets` and select `Snippets:
Configure User Snippets`, then type/select `Lean`. This will create a
`lean.json` file, which you can replace with
`https://github.com/ianjauslin-rutgers/pythagoras/tree/master/snippets/lean.json`.
(Alternatively, you can copy `lean.json` to your VSC snippets folder, whose path
might look something like `$HOME/.config/VSCodium/User/snippets`, at least on Ubuntu.)

## Coding style

### Theorem indentation

When stating a theorem or lemma, use the following indentation:

```lean
theorem name_of_theorem {arguments} (more arguments)
    (more arguments) :
    statement := by
  proof...
```

### Rough hierarchy of arguments

The logic behind this is that the more fundamental a concept, the higher is should be on the list.

- `point`
- `line`
- `circle`
- `length_type`
- `angle_type`
- `area_type`
- `online`
- `B`
- `sameside`
- `diffside`
- `cen_circ`
- `in_circ`
- `oncircle`
- `lines_inter`
- `line_circle_inter`
- `circles_inter`
- `length`
- `angle`
- `rightangle`
- `area`
- `eq_tri`

### Naming conventions (to be discussed further)

The following naming conventions are used for variables. Note that when most of these notations are used for functions that end in Prop, both the term and the negation of the term may carry the same name. This helps with proofs by cases. For example, `aL` can refer to either `online a L` or `¬ online a L`. Since only one of these is ever true, and since the reader should be following with a diagram this should not cause much confusion.

- `a b c d e` are points  (in general, lowercase Roman letters)
- `L M` are lines (in general, uppercase Roman letters)
- `α β` are circles (in general, lowercase Greek letters)
- `ab` means `a ≠ b`
- `aL` means `online a L`
- `Babc` means `B a b c`
- `abL` means `sameside a b L`
- `aLb` means `diffside a b L`
- `aα` means either that `cen_circ a α` or `oncircle a α` (note that at most one of these can be true for any given circle)
- `ab_cd` means `length a b = length c d`
- `αβ` means that`circles_inter α β`

## Building the project

The project can be built using

```bash
lake build
```

This will compile all the project files, but will not show warnings or errors.
To show those, use

```bash
lake --verbose build
```

In reality, `lake build` only compiles one file: `Pythagoras.lean` which
imports all the project files. `Pythagoras.lean` can be generated automatically
by running

```bash
./scripts/gen_basefile
```
