require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7119665 [A] : Prf (∀ (λ u : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (= ((@sum A) s u) (real_of_num (NUMERAL _0)))) (∨ (∀ (λ i : El A, (⇒ ((@IN A) i s) (= (u i) (real_of_num (NUMERAL _0)))))) (∃ (λ j : El A, (∃ (λ k : El A, (∧ ((@IN A) j s) (∧ (real_lt (u j) (real_of_num (NUMERAL _0))) (∧ ((@IN A) k s) (real_gt (u k) (real_of_num (NUMERAL _0))))))))))))))));
