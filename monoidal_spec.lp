require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5712802 [A] : Prf (∀ (λ op : El (fun A (fun A A)), (= ((@monoidal A) op) (∧ (∀ (λ x : El A, (∀ (λ y : El A, (= (op x y) (op y x)))))) (∧ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ z : El A, (= (op x (op y z)) (op (op x y) z)))))))) (∀ (λ x : El A, (= (op ((@neutral A) op) x) x))))))));
