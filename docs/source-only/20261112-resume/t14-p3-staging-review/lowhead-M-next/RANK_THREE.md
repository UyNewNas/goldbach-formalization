# Independent arithmetic for an occupied three-slot box

Write \(a,b,c\) for the logarithms to base \(x\) of the ordered integer upper endpoints of the three rough slots. Let \(u=\log_x U\), \(s\) bound the log-size of the original small Rosser factor in group 3, and \(r=\log_x|T|\). The source-side joins to check are

\[
 0\le a,b,c\le h=49/250,\quad a+b+3c\le d=3/5,\quad
 2\eta\le u\le 1/3+\eta/2,\quad 0\le s\le\eta/16 .
\]

The first slot must actually be in group 2. This demands both the matching `none` branch of `choice` and \(D/(Ax^a)\ge1\) for \(A=x^{u-\eta}\). Dyadic owners are always at most the corresponding occupied arithmetic values. Denote by \(q_i\) the resulting upper bounds on \(\log_x Q_i\). In all four cases \(q_1\le u-\eta\), which yields the strict first inequality for \(\sigma<\eta\).

The three other left-hand exponents are \(E_2=2u+q_2+2q_3\), \(E_3=(7/32)r+u+q_1+5q_2+2q_3\), and \(E_4=23u/16+q_1+73q_2/16+39q_3/16\). The following bounds keep the original order of the two residual slots.

| Residual slots accepted on the left | Upper exponents \((q_1,q_2,q_3)\) | \(E_2\) at most | \(E_3-(7/32)r\) at most | \(E_4\) at most |
| --- | --- | --- | --- | --- |
| Both | \((b+c,a,s)\) | \(2u+h+2s\) | \(2u+5h+2s\) | \(39u/16+73h/16+39s/16\) |
| Only \(b\) | \((b,a,c+s)\) | \(d+2h+2\eta+2s\) | \(d+5h+\eta+2s\) | \(23d/16+66h/16+23\eta/16+39s/16\) |
| Only \(c\) | \((c,a,b+s)\) | \(5h+2\eta+2s\) | \(9h+\eta+2s\) | \(151h/16+23\eta/16+39s/16\) |
| Neither | \((0,a,b+c+s)\) | \(d+2h+2\eta+2s\) | \(d+5h+\eta+2s\) | \(23d/16+66h/16+23\eta/16+39s/16\) |

For example, rejection of \(c\) after acceptance of \(b\) gives \(u<b+c+\eta\), and rejection of both gives \(u<c+\eta\). In each case the second exponent is bounded using \(a+2b+4c=(a+b+3c)+(b+c)\). The last exponent uses \(73a/16+39b/16+62c/16\le 23(a+b+3c)/16+50a/16+b\). Rejection of \(b\) followed by acceptance of \(c\) gives \(u<b+\eta\). When both enter the first group, the sum of their exponents is at most \(u-\eta\).

In particular \(d+2h=124/125\). The elementary exponent bounds already suffice with \(0<\eta\le1/400\), \(\sigma=\eta/100\), \(0<\kappa\le\eta/10000\) and \(r\le1+3\kappa\). In the row where only \(c\) enters the left bin, the baseline part of \(E_3\) is \(7/32+9h=1.98275\). The selected physical theorem uses \(\eta=\zeta\le1/20000\), \(\sigma=\zeta/2000\), \(\kappa\le\zeta/200000\), and \(r\le1+\kappa\). Its fine-label hypotheses establish the displayed input bounds in that parameter range. These values give the manuscript inequality \(\kappa\le\sigma/100\) and strict slack in each of \(E_2<1-8\sigma\), \(E_3<2-15\sigma\), and \(E_4<2-15\sigma\).
