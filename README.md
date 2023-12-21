# Binary Search Tree in TLA+

This repository contains a TLA+ specification for a Binary Search Tree (BST) using a finite set of natural numbers. The implementation supports basic operations like insertion and deletion while maintaining BST properties.

## Features

- **Finite Natural Numbers**: Operates on a set of natural numbers (`FNat`) ranging from 0 to 7 (or any other natural number).
- **Core Operations**: Includes `Insert` and `Delete` functions.
- **Property Verification**: Ensures type correctness, parent-child relationship integrity, reachability from the root, and sorting invariant of BST.
- **State Variables**: `root`, `nodes`, `parent`, `left`, `right` defining the tree structure.

## Getting Started

### Prerequisites

- TLA+ tools including the TLA+ Toolbox. Download from [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html).

### Running the Specification

Load the specification file in TLA+ Toolbox and use the TLC model checker to verify the BST's invariants and behavior.

## Usage

- `Insert(n)`: Insert a number `n` into the BST.
- `Delete(n)`: Remove a number `n` from the BST.
- Verify correctness with the model checker.
