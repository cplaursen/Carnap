# carnap-check

A command-line tool for checking natural deduction proofs using the Carnap proof-checking library, without needing to run the web server.

## Building

To build the tool, run:
```bash
stack build Carnap:exe:carnap-check
```

To install the tool, run:
```bash
stack install Carnap:exe:carnap-check
```

Then, it will be available as `carnap-check` in your PATH.

## Usage

```
carnap-check <system> <file>
carnap-check --list # lists all available systems
```

- `<system>` — the name of the logical system to check against (e.g. `prop`, `firstOrder`)
- `<file>` — path to a plain-text file containing the proof

## Examples
If file `carnap-proof.txt` contains:

```
P /\ Q :PR
P :/\E 1
Q :/\E 1
~Q \/ R :PR
  ~Q :AS
  _|_ :~E 5,3
  R :X 6
--
  R :AS
  R :R 9
R :\/E 4,5-7,9-10
(P /\ Q) /\ R :/\I 1,11
```

You would run:

```bash
carnap-check fosterAndLaursenTFL carnap-proof.txt
```

To see output `Proven: (P ∧ Q), (¬Q ∨ R) ⊢ ((P ∧ Q) ∧ R)`