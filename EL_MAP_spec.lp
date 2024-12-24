require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1207492 [_28366 _28367] : Prf (∀ (λ f : El (fun _28367 _28366), (∀ (λ n : El num, (∀ (λ l : El (list _28367), (⇒ (< n ((@LENGTH _28367) l)) (= ((@EL _28366) n ((@MAP _28367 _28366) f l)) (f ((@EL _28367) n l))))))))));
