require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4807107 [_110698] : Prf (∀ (λ r : El (fun _110698 (fun _110698 bool)), (∀ (λ x : El _110698, (∀ (λ s : El (fun _110698 bool), (= ((@pairwise _110698) r ((@INSERT _110698) x s)) (∧ (∀ (λ y : El _110698, (⇒ (∧ ((@IN _110698) y s) (¬ (= y x))) (∧ (r x y) (r y x))))) ((@pairwise _110698) r s)))))))));
