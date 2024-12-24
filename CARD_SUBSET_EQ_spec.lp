require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3900203 [A] : Prf (∀ (λ a : El (fun A bool), (∀ (λ b : El (fun A bool), (⇒ (∧ ((@FINITE A) b) (∧ ((@SUBSET A) a b) (= ((@CARD A) a) ((@CARD A) b)))) (= a b))))));
