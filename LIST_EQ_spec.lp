require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1116330 [A] : Prf (∀ (λ l1 : El (list A), (∀ (λ l2 : El (list A), (= (= l1 l2) (∧ (= ((@LENGTH A) l1) ((@LENGTH A) l2)) (∀ (λ n : El num, (⇒ (< n ((@LENGTH A) l2)) (= ((@EL A) n l1) ((@EL A) n l2)))))))))));
