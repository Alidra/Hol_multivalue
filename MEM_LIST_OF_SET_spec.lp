require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4788386 [A] : Prf (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (∀ (λ x : El A, (= ((@MEM A) x ((@list_of_set A) s)) ((@IN A) x s)))))));
