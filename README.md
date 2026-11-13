<h1 align="center">
  Dynamic metastability in the self-attention model
</h1>

<tt>Lean</tt> proofs accompanying the revised version of the paper
**[Dynamic metastability in the self-attention model](https://arxiv.org/abs/2410.06833)** by Borjan Geshkovski, Hugo Koubbi, Yury Polyanskiy and Philippe Rigollet.

The main theorem is [`SourceMain.main_and_cascade`](Metastability/SourceMain.lean): the energy staircase, collision windows and deterministic empirical-measure limits for both self-attention models, with transport expressed through finite couplings.

## Verification

With [elan](https://github.com/leanprover/elan) installed, run:

```sh
lake exe cache get
lake build
```

## Citing

```bibtex
@misc{geshkovski2024dynamic,
  title={Dynamic metastability in the self-attention model},
  author={Borjan Geshkovski and Hugo Koubbi and Yury Polyanskiy and Philippe Rigollet},
  year={2024},
  eprint={2410.06833},
  archivePrefix={arXiv},
  primaryClass={cs.LG},
  url={https://arxiv.org/abs/2410.06833}
}
```
