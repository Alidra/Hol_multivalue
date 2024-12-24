require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem365156 [A] : Prf (∀ (λ H : El (fun (fun num A) (fun num A)), (⇒ (∀ (λ f : El (fun num A), (∀ (λ g : El (fun num A), (∀ (λ n : El num, (⇒ (∀ (λ m : El num, (⇒ (< m n) (= (f m) (g m))))) (= (H f n) (H g n))))))))) (∃ (λ f : El (fun num A), (∀ (λ n : El num, (= (f n) (H f n)))))))));
