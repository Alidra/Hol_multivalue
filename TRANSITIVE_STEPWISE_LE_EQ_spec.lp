require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem290135 : Prf (∀ (λ R : El (fun num (fun num bool)), (⇒ (∧ (∀ (λ x : El num, (R x x))) (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ z : El num, (⇒ (∧ (R x y) (R y z)) (R x z))))))))) (= (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (R m n)))))) (∀ (λ n : El num, (R n (SUC n))))))));
