require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6897351 [A] : Prf (∀ (λ dom : El (fun A bool), (∀ (λ neut : El A, (∀ (λ op : El (fun A (fun A A)), (∀ (λ f : El (fun num A), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@iterato A num) dom neut op <= (… m n) f) ((@COND A) (<= m n) ((@COND A) (⇒ ((@IN A) (f m) dom) (= (f m) neut)) ((@iterato A num) dom neut op <= (… (+ m (NUMERAL (BIT1 _0))) n) f) (op (f m) ((@iterato A num) dom neut op <= (… (+ m (NUMERAL (BIT1 _0))) n) f))) neut))))))))))))));
