# Step by Step Instructions


## Testing the examples shown in the paper




## Experimenting with MLscript

The simplest way of experimenting with MLscript is to use the existing testing infrastructure.
(The web demo could also be used, but it is hosted externally;
alternatively, it can be run locally by following the instructions in `README.md`,
though that's not the way we recommend for easy experimentation.)

The way testing works is as follows:
 - the MLscript compiler reads the test file one code block at a time (code blocks are separated by empty lines);
 - after reading a code block, it outputs the corresponding inferred types, as well as any encountered type errors;
 - after that, it executes the code block through NodeJS (by shelling out to the `node` process) and outputs the results.
 
Test output is inserted **in place** in the test file after each corresponding block, as comments beginning with `//│`.
This makes it very easy and convenient to see the test results for each code block.
For this reason,
we recommend an editor that automatically reloads open files on changes. VSCode and Sublime Text work well for this.

The testing infrastructure is set up so that if there are any unstaged changes in any test file
(in `shared/src/test/diff`), only the corresponding files will be run.

So you can make select modifications to some test files and run the test command again,
and it will only test your modified test.

You can also run the tests continuously using the SBT command `~mlscriptJVM/testOnly mlscript.DiffTests`,
which will watch for any changes in the project and re-run the tests automatically.





