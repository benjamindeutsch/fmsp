# LeanSPI

A lean formalization of the paper [_Types for Security Protocols_](https://web.cs.wpi.edu/~guttman/cs559_website/chapter-7.pdf) by M. Maffei and R. Focardi.

## Usage

The library depends on Mathlib, so compiling the project requires compiling the entirety of Mathlib (which may take a while).
To avoid this extra step, we can download a precompiled cached version of mathlib with the following commands:
```
lake exec cache get
lake build
```
