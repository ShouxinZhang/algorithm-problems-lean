# Repository Structure

## Top Level
- AlgorithmProblems/
- docs/
- .lake/
- .github/
- .vscode/
- README.md
- LICENSE
- lakefile.toml
- lake-manifest.json
- lean-toolchain

## AlgorithmProblems
- AlgorithmProblems/MathStatement/ 题面描述
- AlgorithmProblems/Formalize/ Lean4 形式化

## AlgorithmProblems/Formalize
- AlgorithmProblems/Formalize/BridgeAndTorch.lean（桥与火把题面：状态/转移与贪心规格）
- AlgorithmProblems/Formalize/ClimbingStairs.lean（paths 为集合规范，递推通过 pathsSplit/pathsJoin 与 Nat.card 对齐）
