# Step by Step Instructions


## Testing the examples shown in the paper


The test file `shared/src/test/diff/mlscript/Paper.mls` contains the main examples shown in the paper,
which are all contained within its first two sections.

Some inferred types might be a little different due to small type simplifier quirks
(for example the test file shows `0 | int & ~0` instead of `int`),
but it should be easy to check that they are equivalent.
As another example, in the paper, we show the type `Some['a] | None`
and in the test it appears as `None | Some[?] & {value: 'a}`,
but the two are equivalent (they have the same structural decomposition).

There were a few typos in the original submission (corrected since then).
For example, in the paper we sometimes forgot the braces in `None{}`.
These small things have been fixed in the test file.

We encourage artifact reviewers to try variations of these examples
and see how the inferred types change and what errors are reported.


## Experimenting with MLscript

The simplest way of experimenting with MLscript is to use the existing testing infrastructure of the project.
(The web demo could also be used, but it is hosted externally (at https://hkust-taco.github.io/mlscript/);
alternatively, this demo can be run locally by following the instructions in `README.md`,
though that's not the way we recommend for the easiest experimentation.)

The way testing works in MLscript is as follows:
 - the MLscript compiler reads a given test file one code block at a time (code blocks are separated by empty lines);
 - after reading a code block, it outputs the corresponding inferred types, as well as any encountered type errors;
 - after that, it executes the code block through NodeJS (by shelling out to the `node` process) and outputs the results.
 
Test output is inserted **in place** in the test file after each corresponding block, as comments beginning with `//│`.
This makes it very easy and convenient to see the test results for each code block.
For this reason, we recommend using an editor that automatically reloads open files on changes. VSCode and Sublime Text work well for this.

The testing infrastructure is set up so that if there are any unstaged changes (as determined by `git`) in any test file
(those in `shared/src/test/diff`), only the corresponding files will be tested.
So you can make select modifications to some test files and run the test command again,
and it will only run your modified tests.

You can also run the tests continuously using the SBT command `~mlscriptJVM/testOnly mlscript.DiffTests`,
which will watch for any changes in the project and re-run the tests automatically.



