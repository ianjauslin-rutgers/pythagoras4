# Lean Seminar project: Many proofs of the Pythagoras theorem

## Setting up the project

Authorization is needed to contribute to this project. If you are having
issues, contact Ian.

To download the project, run

```bash
git clone https://github.com/ianjauslin-rutgers/pythagoras4.git && lake update && lake exe cache get
```

or, if you prefer to use SSH,

```bash
git clone git@github.com:ianjauslin-rutgers/pythagoras4.git && lake update && lake exe cache get
```

This will download all the files in the project and install a copy of **mathlib**
in the project directory, along with its oleans. You should now be all set to
start working!

## Importing Andre's API

To use Andre's API, add the following at the top of your file:

```lean
import synthetic
open incidence_geometry
```

This may take some time, as the synthetic file needs to be compiled when it is
imported. Instead, if you only need the axioms, but not the theorems from
Andre's API, you can use

```lean
import synthetic_axioms
open incidence_geometry
```

instead.

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
where it can be merged with everyone else's), run

```bash
git checkout master
git pull
git merge prop1
git push
```

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

## Rough hierarchy of arguments

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

## Naming conventions (to be discussed further)

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
