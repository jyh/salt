# INSERT (banked for the ratified editing round): the windmill pattern

*JYH-ratified as a paper theme 2026-07-22 ("belongs in the paper").
Target: the Discussion/Methodology section. Status note: instance (3)
is design-complete with an adversarial review in flight at drafting
time — the editing round must update its status to whatever the record
then shows. Draft prose below; JYH's voice pass expected.*

## Draft prose (~300 words)

A recurring phenomenon in this formalization deserves independent
attention: analytic machinery in the source literature repeatedly
dissolved, under formalization, into finite combinatorics. Three
instances. (1) A k!-fold overcounting argument, presented in the
literature via permutation combinatorics, reduced to a nested-
antidiagonal induction on convolution ladders — no permutations appear
in the formal proof. (2) A Shiu-type multiplicative bound, analytic in
its published form, closed along entirely elementary routes (a
factorial-divisor argument replacing the contour). (3) A four-factor
multivariable Perron argument — priced as the campaign's largest
porting risk — reduced to a single Dirichlet series handled by
convolution algebra: the multivariable half of the risk dissolved; the
line-move half genuinely remained.

We offer a three-part explanation. First, a cost-model shift: analytic
compression (a contour shift, a sharp truncation) is cheap ink for a
human reader but expensive in a proof assistant, where interchange
lemmas and decay estimates dominate; finite algebra, costly on paper,
is nearly free before the kernel. Routes that were always available
but never economical become optimal under the new prices. Second, an
exactness dividend: choosing exact kernels over truncated ones
preserves identities that compose algebraically, concentrating the
genuinely analytic content into few, small, late defect terms. Third,
a localization effect: our fail-fast discipline (executors stop rather
than force) repeatedly measured where the true obstruction stood —
twice revealing that the "wall" was an artifact of following the
paper's route too literally.

We equally record the pattern's boundary. A proposed further
dissolution — eliminating the remaining line-move itself — was refuted
by adversarial review before any formal attempt was made, the
refutation resting on structural facts rather than difficulty:
truncated Euler products admit no log-derivative identity, because
window indicators are not multiplicative. The pattern is real but not
universal, and the same discipline that exploits it polices it: the
telescoping a main-term extraction needs lives only in the full
multiplicative series, while convergence past the 1-line lives only in
its truncations, and no algebraic reordering makes one object do both
jobs.

We suggest the pattern is not incidental: formal corpora may
systematically surface proof routes that the economics of print
concealed — and, symmetrically, adversarial formal review can identify
where a seductive dissolution is impossible before any effort is spent
attempting it.

## Editing-round checklist

- Instance (3) + the boundary paragraph are CURRENT as of the
  2026-07-22 refutation (4/4 FATAL, dissolution dead, Lemma-2.5 port
  promoted); update further if the port's own story adds material.
- Cross-reference the specific Lean names if the venue wants them
  (the C-ladder lemmas; the MULT-SHIU module; seam_realignment_hat +
  the W-stones).
- Tone: keep the claim modest ("we suggest"); this is an observation,
  not a theorem.
- JYH voice pass before freeze (the community-voice law applies to
  paper prose read by humans: JYH phrases the final text).
