require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1072128 [A Z] : Prf (∀ (λ NIL' : El Z, (∀ (λ CONS' : El (fun A (fun (list A) (fun Z Z))), (∃ (λ fn : El (fun (list A) Z), (∧ (= (fn (@NIL A)) NIL') (∀ (λ a0 : El A, (∀ (λ a1 : El (list A), (= (fn ((@CONS A) a0 a1)) (CONS' a0 a1 (fn a1))))))))))))));
