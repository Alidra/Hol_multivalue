require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1235505 [A] : Prf (∀ (λ R : El (fun A (fun A bool)), (∀ (λ R' : El (fun A (fun A bool)), (∀ (λ l : El (list A), (⇒ (∧ ((@PAIRWISE A) R l) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@MEM A) x l) (∧ ((@MEM A) y l) (R x y))) (R' x y))))))) ((@PAIRWISE A) R' l))))))));
