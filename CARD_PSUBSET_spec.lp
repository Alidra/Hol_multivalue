require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3921097 [A] : Prf (∀ (λ a : El (fun A bool), (∀ (λ b : El (fun A bool), (⇒ (∧ ((@PSUBSET A) a b) ((@FINITE A) b)) (< ((@CARD A) a) ((@CARD A) b)))))));
