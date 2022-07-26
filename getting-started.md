# Getting Started Guide

This is the MLscript artifact of the paper *MLscript: Principal Type Inference in a Boolean Algebra of Structural Types*. It consists of an SBT (Scala Build Tool) project with an implementation of MLscript and a comprehensive test suite.
The implementation can be compiled both to the JVM and to JavaScript (using ScalaJS), allowing it to be tried in the browser.

- The `shared/src/main/scala/mlscript/` directory contains the sources of the MLscript compiler.

- The `shared/src/test/scala/mlscript` directory contains the sources of the testing infrastructure.

- The `shared/src/test/diff` directory contains the actual tests.


## Prerequisites

To compile the project and run the tests, all you need is a recent Java Virtual Machine (JVM), the Scala Build Tool (SBT), and NodeJS.

The simplest way to set up the JVM and SBT is through the `coursier` tool.
We explicitly support NodeJS versions `v16.14.x`, `v16.15.x`, `v16.16.x`, and `v17.x.x`.

We also provide a Docker image that already contains the required toolchain,
ready to be used.


### Setting up manually

1. Install NodeJS (for example `v16.16.0`) from https://nodejs.org/en/download/.
    Make sure your PATH is updated and the `node` command is available in the terminal.

2. Follow the Coursier installation instructions at https://get-coursier.io/docs/cli-installation.

3. Change your working directory to the root of this repository and launch the SBT shell by typing `sbt` in the terminal.


### Using the Docker image

We have built a Docker image containing all necessary prerequisites and pushed it to [Docker Hub](https://hub.docker.com/r/mlscript/mlscript-docker).

To use this image, you should first install Docker if it is not installed yet. Then, you can launch a container using this image with the following command:

```
docker pull mlscript/mlscript-docker:v0
docker run -it --rm mlscript/mlscript-docker:v0
```

You will be attached to the shell of the container after the image gets pulled and the container is launched.
Please `cd` to `mlscript-core-language/` and launch the SBT shell by typing `sbt`.


## Compiling the project and running the tests

Simply enter `test` in the SBT shell to compile both to the JVM and to JS and run all the tests.
This will automatically download all the necessary dependencies, including the correct Scala compiler version, if needed.

Alternatively, `mlscriptJVM/test` will only compile the JVM version, which should be sufficient.



