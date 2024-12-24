require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1189923 [_27796 _27797 _27798] : Prf (∀ (λ f : El (fun _27798 (fun _27797 _27796)), (∀ (λ l : El (list _27798), (∀ (λ m : El (list _27797), (∀ (λ k : El num, (⇒ (∧ (< k ((@LENGTH _27798) l)) (< k ((@LENGTH _27797) m))) (= ((@EL _27796) k ((@MAP2 _27796 _27798 _27797) f l m)) (f ((@EL _27798) k l) ((@EL _27797) k m))))))))))));
