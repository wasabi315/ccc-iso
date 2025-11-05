# ccc-iso

> [!NOTE]
> Work in progress.

A Cubical Agda formalization of a decider for the following type isomorphisms:

```math
\begin{align*}
  A \times B & = B \times A \\
  A \times (B \times C) & = (A \times B) \times C \\
  A \rightarrow (B \rightarrow C) & = (A \times B) \rightarrow C \\
  A \rightarrow (B \times C) & = (A \rightarrow B) \times (A \rightarrow C) \\
  1 \times A & = A \\
  1 \rightarrow A & = A \\
  A \rightarrow 1 & = 1
\end{align*}
```

## References

- Mikael Rittri. 1989. Using types as search keys in function libraries. In Proceedings of the fourth international conference on Functional programming languages and computer architecture (FPCA ’89), November 01, 1989. Association for Computing Machinery, New York, NY, USA, 174–183. https://doi.org/10.1145/99370.99384
