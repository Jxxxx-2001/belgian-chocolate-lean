# Recompute the rational controller witness

Run the verifier with Python 3.12 from the repository root.

```sh
python verification/verify_schur_standalone.py verification/controller_degree28.json
```

The verifier uses exact integer and rational arithmetic from the standard library. It reconstructs the closed-loop polynomial and checks 28, 28, and 30 strict Schur inequalities for $x,y,Z$, respectively. It writes `controller_degree28_schur_certificate.json` beside the input.

The controller witnesses feasibility at $\delta=98236947/100000000$. It gives a feasible parameter in the range needed for the analytic comparison. The witness is also proved in Lean. [`witness_feasible`](../formalization/ControllerFeasible.lean#L34)
