# Selector combining

Heavy use of custom gates can lead to a circuit defining many binary selectors, which
would increase proof size and verification time.

This page describes an optimization that combines binary selector columns into fewer
fixed columns. The basic idea is that if we have binary selectors $q_1, \ldots, q_k$,
that are enabled on disjoint sets of rows, then under some additional conditions we
can combine them into a single fixed column, say $q'$, such that:
$$
q' = \begin{cases} i, &\text{if } q_i = 1 \\ 0, &\text{if all } q_i \text{ are } 0 \end{cases}
$$

However, the devil is in the detail.

The halo2 API allows defining some selectors to be "simple selectors", subject to the
following condition:

> Every polynomial constraint involving a simple selector $s$ must be of the form
> $s . t = 0$, where $t$ is a polynomial involving *no* simple selectors.

Suppose that $s$ is $q_i$ in some set of simple selectors $q_1, \ldots, q_k$ that
is combined into $q'$ as above. Then this condition ensures that replacing $q_i$ by
$\prod_{j \in \{1..k\} \setminus i} (j - q')$ will not change the meaning of any
constraints.

> It would be possible to relax this condition by ensuring that every use of a
> binary selector is substituted by a precise interpolation of its value from the
> corresponding combined selector. However,
>
> * the restriction simplifies both the implementation, and human understanding of
>   the resulting constraint system;
> * substituting an interpolation at every use of a binary selector could
>   significantly increase the degree of affected constraints;
> * the scope to apply the optimization is not impeded very much by the restriction
>   for typical circuits.
