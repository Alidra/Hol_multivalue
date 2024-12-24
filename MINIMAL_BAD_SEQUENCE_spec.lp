require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem388777 [A] : Prf (∀ (λ << : El (fun A (fun A bool)), (∀ (λ bad : El (fun (fun num A) bool), (⇒ (∧ ((@WF A) <<) (∧ (∀ (λ x : El (fun num A), (⇒ (¬ (bad x)) (∃ (λ n : El num, (∀ (λ y : El (fun num A), (⇒ (∀ (λ k : El num, (⇒ (< k n) (= (y k) (x k))))) (¬ (bad y)))))))))) (∃ (λ x : El (fun num A), (bad x))))) (∃ (λ y : El (fun num A), (∧ (bad y) (∀ (λ z : El (fun num A), (∀ (λ n : El num, (⇒ (∧ (bad z) (∀ (λ k : El num, (⇒ (< k n) (= (z k) (y k)))))) (¬ (<< (z n) (y n))))))))))))))));
