\title{
Degree sequences in triangle-free graphs
}

\author{
Paul Erdós, Siemion Fajtlowicz and William Staton \\ Mathematical Institute, Hungarian Academy of Sciences, Reâltanoda u. 13-15 H-1053 Budapest, Hungary
}

Received 4 January 1989
Revised 19 April 1989
Dedicated to Professor R.G. Stantom on the occasion of his 68th birthday.

\author{
Abstract \\ Erdös, P., S. Fajtlowicz and W. Staton, Degree sequences in triangle-free graphs, Discrete Mathematics 92 (1991) 85-88.
}

The computer program Graffiti has conjectured that the chromatic number of a triangle-free graph does not exceed the maximum number of occurrences of an element of the degree sequence [1]. We prove that indeed if no degree occurs more than twice, the graph is bipartite. On the other hand, we prove that every triangle-free graph is an induced subgraph of a triangle-free graph in which no degree occurs more than three times.

In the two lemmas which follow, we assume that $\left\{d_{i}: 1 \leqslant i \leqslant 4 n+3\right\}$ is a nondecreasing sequence of positive integers and that no three terms are equal. We assume also that all subscripts are appropriately bounded.

Lemma 1. (a) $d_{k+2}-d_{k} \geqslant 1$;
(b) $d_{k+2 r}-d_{k} \geqslant r$.

Proof. (a) is obvious since no three terms are equal.
(b) is an easy induction beginning with (a).

\section*{Lemma 2.}
(a) $\quad \sum_{k=2 n+1}^{4 n} d_{k}-\sum_{k=1}^{2 n} d_{k} \geqslant 2 n^{2}$;
(b) $\quad \sum_{k=2 n+1}^{4 n+1} d_{k}-\sum_{k=1}^{2 n} d_{k} \geqslant 2 n^{2}+2 n+1$;
(c) $\quad \sum_{k=2 n+2}^{4 n+2} d_{k}-\sum_{k=1}^{2 n+1} d_{k} \geqslant 2 n^{2}+2 n$;
(d) $\sum_{k=2 n+2}^{4 n+3} d_{k}-\sum_{k=1}^{2 n+1} d_{k} \geqslant 2 n^{2}+4 n+2$.

Proof.
(a)
$$
\sum_{k=2 n+1}^{4 n} d_{k}-\sum_{k=1}^{2 n} d_{k}=\sum_{k=1}^{2 n}\left(d_{2 n+k}-d_{k}\right) \geqslant \sum_{k=1}^{2 n} n=2 n^{2} .
$$
(b) $\quad \sum_{k=2 n+1}^{4 n+1} d_{k}-\sum_{k=1}^{2 n} d_{k}=d_{4 n+1}+\sum_{k=2 n+1}^{4 n} d_{k}-\sum_{k=1}^{2 n} d_{k}$
$$
\begin{aligned}
& \geqslant d_{4 n+1}+2 n^{2} \\
& \geqslant 2 n+1+2 n^{2} .
\end{aligned}
$$
(c) $\quad \sum_{k=2 n+2}^{4 n+2} d_{k}-\sum_{k=1}^{2 n+1} d_{k}=d_{4 n+2}-d_{2 n+1}+\sum_{k=1}^{2 n+1}\left(d_{2 n+k}-d_{k}\right)$
$$
\begin{aligned}
& \geqslant d_{4 n+2}-d_{2 n+2}+\sum_{k=1}^{2 n+1}(n) \\
& \geqslant n+(2 n+1) n=2 n^{2}+2 n .
\end{aligned}
$$
(d)
$$
\begin{aligned}
\sum_{k=2 n+2}^{4 n+3} d_{k}-\sum_{k=1}^{2 n+1} d_{k} & =d_{4 n+3}+\left(\sum_{k=2 n+2}^{4 n+2} d_{k}-\sum_{k=1}^{2 n+1} d_{k}\right) \\
& \geqslant 2 n+2+\left(2 n^{2}+2 n\right)=2 n^{2}+4 n+2 .
\end{aligned}
$$ \(\square\)

Note that for equality to hold in any of the statements of Lemma 2, the sequence must be such that $d_{k+2}-d_{k}=1$ for all appropriately bounded $k$. This condition implies that there are no 'gaps' in the sequence and that every term appears exactly twice with the possible exceptions of the first and last terms, which may appear either once or twice. Sequences satisfying $d_{k+2}-d_{k}=1$ for all $k$ will be called compact. Note that compact sequences are determined by their first two terms. For a graph $G$, we define $f=f(G)$ to be the maximum number of occurrences of any term of the degree sequence of $G$. As usual, $\delta=\delta(G)$ is the smallest element of the degree sequence of $G$. In order to avoid trivialities, we assume our graphs have no isolated vertices.

Theorem 1. Let $G$ be a triangle-free graph with $f(G)=2$. Then $G$ is bipartite, $\delta(G)=1$, and the degree sequence of $G$ is compact.

Proof. Suppose $G$ has $4 n$ vertices, $v_{1}, \ldots, v_{4 n}$, with degree sequence $d_{1}, \ldots, d_{4 n}$ in nondecreasing order. Let $H$ be the subgraph induced by $v_{2 n+1}, \ldots, v_{4 n}$. The number of edges in $H$ is at least
$$
\frac{1}{2}\left(\sum_{k=2 n+1}^{4 n} d_{k}-\sum_{k=1}^{2 n} d_{k}\right),
$$
with equality only in case the vertices not in $H$ send all their edges into $H$. By Lemma 2(a), this is at least $n^{2}$ edges, with equality only in case the degree sequence of $G$ is compact. But $H$ is triangle-free with $2 n$ vertices, so Turan's theorem forces the conclusion that $H$ is $K_{n, n}$ and that the degree sequence of $G$ is indeed compact. Consider the vertices $v_{1}, \ldots, v_{2 n}$ not in $H$. If $(X, Y)$ is the bipartition of $H$, then, since $G$ is triangle-free, no $v_{i}(1 \leqslant i \leqslant 2 n)$ sends edges into both $X$ and $Y$. Hence each $v_{i}$ may be placed either with $X$ or with $Y$ to form a bipartition of $G$. Since the vertices $v_{i}(1 \leqslant i \leqslant 2 n)$ have degrees not exceeding $n$, it follows that $\delta=1$. This concludes the proof in case $G$ has $4 n$ vertices. In case $G$ has $4 n+2$ or $4 n+3$ vertices, the proof is nearly identical, using Lemma 2 (c) and (d). In case $G$ has $4 n+1$ vertices, we let $H$ be the subgraph induced by $v_{2 n+1}, \ldots, v_{4 n+1}$ and note that by Lemma 2(b), $H$ has at least $n^{2}+n+\frac{1}{2}$ edges. Turan's theorem forbids this. It follows that no triangle-free graph with $4 n+1$ vertices may have $f(G)=2$.

We have seen that triangle-free graphs $G$ with $f(G)=2$ must have $\delta=1$. It is natural to ask whether an upper bound on $f(G)$ imposes an upper bound on $\delta$.

Lemma 3. For every positive integer $n$ there is a bipartite graph $G$ with $8 n$ vertices, $\delta=n+1$, and $f(G)=3$.

Proof. Let $G$ have vertices $x_{i}$ and $y_{i}$ for $1 \leqslant i \leqslant 4 n$. Join $x_{i}$ to $y_{j}$ with an edge if one of these conditions holds:
(i) $i+j \geqslant 4 n+1$;
(ii) $1 \leqslant i \leqslant j$ and $1 \leqslant j \leqslant n$;
(iii) $1 \leqslant i \leqslant n$ and $2 n+1 \leqslant j \leqslant 3 n$.

It is easy to verify that $G$ has the desired properties.
Lemma 4. Let $G$ be a triangle-free graph with $n$ vertices and let $v$ be a vertex of $G$. There exists a triangle-free graph $H$ containing $G$ as an induced subgraph such that:
(i) the degree of $v$ in $H$ is one more than its degree in $G$;
(ii) for every vertex $w$ of $G$ other than $v$ the degree of $w$ in $H$ is the same as its degree in $G$;
(iii) if $J$ is the subgraph of $H$ induced by the vertices not in $G$, then $f(J)=3$ and $\delta(J) \geqslant 2 n$.

Proof. Let $J$ be a bipartite graph with $f(J)=3$ and $\delta(J) \geqslant 2 n$. Form $H$ by taking the disjoint union of $G$ and $J$ and joining $v$ to some vertex of maximum degree in J. H clearly has the desired properties.

Theorem 2. Every triangle-free graph $G$ is an induced subgraph of a triangle-free graph $H$ with $f(H)=3$.

Proof. Iterate the procedure of Lemma 4 as often as needed, each time increasing the degree of some vertex of $G$ by one. There is room to spread the degrees sufficiently, since in each imbedding the degrees of vertices not in $G$ are much larger than the degrees in $G$. \(\square\)

The imbedding of Theorem 2 is wildly inefficient. If $G$ has $n$ vertices, our construction in Lemma 4 yields a graph $H$ with roughly $17 n$ vertices. In the worst case, where $G$ is regular, $c n^{2}$ iterations are required, so that the final supergraph has something like $n\left(\exp \left(c n^{2}\right)\right)$ vertices. We would like to know whether there are relatively small triangle-free graphs with chomatic number $n$ and $f=3$. In particular, we define $F(n)$ to be the smallest $p$ such that there is a triangle-free graph on $p$ vertices with chromatic number $n$ and $f=3$. The graph obtained by joining end-vertices to two vertices of a pentagon shows that $F(3)=7$. We will show that $F(4) \leqslant 19$. We use the notation $d^{a}$ to indicate that degree $d$ occurs with frequency $a$. Begin with the Grötzsch graph, which has 11 vertices, chromatic number 4 , no triangle, and degree sequence $3^{5} 4^{5} 5^{1}$. Join a new vertex of degree 2 to two non-adjacent vertices of degree 4 to obtain a graph with degree sequence $2^{1} 3^{5} 4^{3} 5^{3}$. The vertices of degree 3 are independent, so we may create three new vertices of degree 5 , joining each to the vertices of degree 3. This yields degree sequence $2^{1} 4^{3} 5^{6} 6^{5}$. Now create three new vertices of degree 3, joining each to the three vertices of degree 5 just created. This yields $2^{1} 3^{3} 4^{3} 5^{3} 6^{5} 8^{3}$. Finally, create a new vertex of degree 2 and join it to two non-adjacent vertices of degree 6 . This yields $2^{2} 3^{3} 4^{3} 5^{3} 6^{3} 7^{2} 8^{3}$. This final graph is triangle-free, has 19 vertices, chromatic number 4 and $f=3$. Hence $F(4) \leqslant 19$. This graph is the smallest counterexample we know to the original conjecture of Graffiti.

\section*{References}
[1] Graffiti, Written on the wall, Conjecture 67, February 1987.
