require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1231070 [A] : Prf (∀ (λ R : El (fun A (fun A bool)), (∀ (λ l : El (list A), (∀ (λ m : El (list A), (= ((@PAIRWISE A) R ((@APPEND A) l m)) (∧ ((@PAIRWISE A) R l) (∧ ((@PAIRWISE A) R m) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@MEM A) x l) ((@MEM A) y m)) (R x y)))))))))))))));
