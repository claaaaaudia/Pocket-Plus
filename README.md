# Pocket+

Reference Haskell implementation of **Pocket+** ([CCSDS 124.0-B-1](https://ccsds.org/publications/bluebooks/entry/3213/), February 2023) for lossless compression of fixed-length spacecraft housekeeping telemetry.

The code is written in **Literate Haskell** and designed to support formal correctness proofs using relational algebra.

---

## Context

- Suggested by **Telespazio** as a formal verification of the Pocket+ protocol.
- Originally started as a Bachelor's final project (February 2025) and continued in a Master's Formal Methods course.

The goal is to provide a clear implementation of the Pocket+ Encoder and Decoder and produce a formal specification and proofs that core components compose correctly.

Engineers can use this implementation as a reference due to its simplicity and the way Haskell's algebraic data types and pattern matching closely mirror the structures defined in the CCSDS specification, keeping the implementation close to the formal model. Each structure is followed by a clear diagram to aid comprehension.

## Status

| Area                  | Status                                  |
|------------------------|------------------------------------------|
| Resynchronization      | Not implemented yet                     |
| Proofs                 | In progress, focused on the run-length encoding component |

## How to Read the Code

- Open the `.lhs` file in a text editor to read the documentation and code side by side or compile as a PDF:
    ```sh
    lhs2TeX pocket.lhs > pocket.tex
    pdflatex pocket.tex
    bibtex pocket
    pdflatex pocket.tex
    pdflatex pocket.tex
    ```

- Use GHC or GHCi to load the source if you want to compile:

  ```sh
  ghci 
  :l Pocket.lhs
  ```
  To test, simply run:
  ```sh
  testEncoder
  testDecoder
  ```
  Additional information about these tests can be found in the .lhs report.

## License

See [LICENSE](./LICENSE) for licensing details.

## Contact

For questions or collaboration, please open an issue in this repository.
