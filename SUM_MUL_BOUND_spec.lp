require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7177890 [A] : Prf (∀ (λ a : El (fun A real), (∀ (λ b : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ i : El A, (⇒ ((@IN A) i s) (∧ (real_le (real_of_num (NUMERAL _0)) (a i)) (real_le (real_of_num (NUMERAL _0)) (b i))))))) (real_le ((@sum A) s (λ i : El A, (real_mul (a i) (b i)))) (real_mul ((@sum A) s a) ((@sum A) s b))))))))));
