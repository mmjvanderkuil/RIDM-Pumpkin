# Build
cargo build --release

# Run nqueens.rs example
cargo run --example nqueens -- 8

# Run minizinc
minizinc --solver pumpkin ./instances/test.mzn
minizinc --solver pumpkin ./instances/learned_nogood.mzn

# Experiments
first compile .mzn to .fzn
minizinc --compile --solver pumpkin learned_nogood.mzn -o learned_nogood.fzn
then run with
cargo run -q -p pumpkin-solver --bin pumpkin-solver -- test.fzn -s