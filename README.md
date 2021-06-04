# fridge

Compiler for molecular circuits
  which compiles circuits by
  optimizing for the sequences
  already synthesized
  and present
  in your fridge.

## Quick Start

These commands will build the Docker image and run the Rust unit tests.

```bash
git clone <this repo>
cd <this repo>
docker build -t fridge-compiler .
docker run -it fridge-compiler cargo test
```
