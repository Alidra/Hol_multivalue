require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7637129 [A B] : Prf (∀ (λ x : El (finite_sum A B), (∃ (λ x' : El num, (∧ (= x ((@mk_finite_sum A B) x')) ((@IN num) x' (… (NUMERAL (BIT1 _0)) (+ ((@dimindex A) (@UNIV A)) ((@dimindex B) (@UNIV B))))))))));
