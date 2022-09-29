_This repository contains an implementation of **MLstruct**, the Boolean-algebraic core of [MLscript](https://github.com/hkust-taco/mlscript). It is relatively faithful to the OOPSLA 2022 paper **[MLstruct: Principal Type Inference in a Boolean Algebra of Structural Types](https://2022.splashcon.org/details/splash-2022-oopsla/41/MLstruct-Principal-Type-Inference-in-a-Boolean-Algebra-of-Structural-Types)**. To obtain MLstruct, we started from the full MLscript language prototype and removed most of the extra features/bells and whistles, and made some extra simplifications._

# MLstruct

What would TypeScript look like if it had been designed with type inference and soundness in mind?

We provide one possible answer in MLscript, an object-oriented and functional programming language with records, generic classes, mix-in traits, first-class unions and intersections, instance matching, and ML-style principal type inference.
These features can be used to implement a form of extensible variants that is as powerful as but also more flexible than unification-based approaches using row variables.

MLstruct supports union, intersection, and complement (or negation) connectives. We make sure they form a Boolean algebra and add enough structure to derive a sound and complete type inference algorithm. For more details, please see the paper mentioned above.


## [Getting Started Guide](getting-started.md)


## [Step by Step Instructions](step-by-step.md)


## Commands Summary

### Running the tests

Running the tests only requires the Scala Build Tool and NodeJS installed.
In the terminal, run `sbt mlscriptJVM/test`.

To run the regression tests continuously as you develop,
launch the SBT shell first with `sbt` and then type `~mlscriptJVM/testOnly mlscript.DiffTests`.

### Running the web demo locally

To run the web demo on your computer, compile the project with `sbt fastOptJS`, then open the `local_testing.html` file in your browser.

You can make changes to the type inference code
in `shared/src/main/scala/mlscript`,
have it compile to JavaScript on file change with command
`sbt ~fastOptJS`,
and immediately see the results in your browser by refreshing the page with `F5`.
