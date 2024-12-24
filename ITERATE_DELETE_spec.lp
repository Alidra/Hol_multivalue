require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5824997 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ a : El A, (⇒ (∧ ((@FINITE A) s) ((@IN A) a s)) (= (op (f a) ((@iterate B A) op ((@DELETE A) s a) f)) ((@iterate B A) op s f))))))))))));
