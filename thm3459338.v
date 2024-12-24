Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459338_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3459015_spec.
Require Import thm3459016_spec.
Require Import thm3459022_spec.
Require Import thm3459023_spec.
Require Import thm3459028_spec.
Require Import thm3459029_spec.
Lemma lem3459196 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3459029 A s x) (@lem3459028 A s x)). Qed.
Lemma lem3459197 {_89769 : Type'} (s : type686 _89769) (x : _89769) : (term0 _89769 x s) = (term1 _89769 s x).
Proof. exact (@lem3459196 _89769 s x). Qed.
Lemma lem3459198 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term2 _89769 _89788 _89789 x P f) = (term3 _89769 _89788 _89789 P f x).
Proof. exact (@lem3459197 _89769 (term4 _89769 _89788 _89789 P f) x). Qed.
Lemma lem3459206 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term5 _83064 x P) = (term6 _83064 P x).
Proof. exact (EQ_MP (@lem3459023 _83064 P x) (@lem3459022 _83064 P x)). Qed.
Lemma lem3459207 {_89769 : Type'} (P : type909 _89769) (x : _89769 -> Prop) : (term7 _89769 x P) = (term8 _89769 P x).
Proof. exact (@lem3459206 (_89769 -> Prop) P x). Qed.
Lemma lem3459208 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (t : _89769 -> Prop) : (term9 _89769 _89788 _89789 t P f) = (term10 _89769 _89788 _89789 P f t).
Proof. exact (@lem3459207 _89769 (term11 _89769 _89788 _89789 P f) t). Qed.
Lemma lem3459209 {_89769 _89788 _89789 : Type'} (GEN_PVAR_57 : _89769 -> Prop) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term12 _89769 _89788 _89789 P f GEN_PVAR_57) = (term13 _89769 _89788 _89789 GEN_PVAR_57 P f).
Proof. exact (eq_refl (term12 _89769 _89788 _89789 P f GEN_PVAR_57)). Qed.
Lemma lem3459210 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term14 _89769 _89788 _89789 P f) = (term15 _89769 _89788 _89789 P f).
Proof. exact (fun_ext (fun GEN_PVAR_57 : _89769 -> Prop => @lem3459209 _89769 _89788 _89789 GEN_PVAR_57 P f)). Qed.
Lemma lem3459211 {_89769 : Type'} : (@GSPEC (_89769 -> Prop)) = (@GSPEC (_89769 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_89769 -> Prop))). Qed.
Lemma lem3459212 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term16 _89769 _89788 _89789 P f) = (term4 _89769 _89788 _89789 P f).
Proof. exact (MK_COMB (@lem3459211 _89769) (@lem3459210 _89769 _89788 _89789 P f)). Qed.
Lemma lem3459213 {_89769 : Type'} (t : _89769 -> Prop) : (@IN (_89769 -> Prop) t) = (@IN (_89769 -> Prop) t).
Proof. exact (eq_refl (@IN (_89769 -> Prop) t)). Qed.
Lemma lem3459214 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term9 _89769 _89788 _89789 t P f) = (term17 _89769 _89788 _89789 t P f).
Proof. exact (MK_COMB (@lem3459213 _89769 t) (@lem3459212 _89769 _89788 _89789 P f)). Qed.
Lemma lem3459215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459216 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term18 _89769 _89788 _89789 t P f) = (term19 _89769 _89788 _89789 t P f).
Proof. exact (MK_COMB (@lem3459215) (@lem3459214 _89769 _89788 _89789 t P f)). Qed.
Lemma lem3459217 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term10 _89769 _89788 _89789 P f t) = (term20 _89769 _89788 _89789 t P f).
Proof. exact (eq_refl (term10 _89769 _89788 _89789 P f t)). Qed.
Lemma lem3459218 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : ((term9 _89769 _89788 _89789 t P f) = (term10 _89769 _89788 _89789 P f t)) = ((term17 _89769 _89788 _89789 t P f) = (term20 _89769 _89788 _89789 t P f)).
Proof. exact (MK_COMB (@lem3459216 _89769 _89788 _89789 t P f) (@lem3459217 _89769 _89788 _89789 t P f)). Qed.
Lemma lem3459219 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term17 _89769 _89788 _89789 t P f) = (term20 _89769 _89788 _89789 t P f).
Proof. exact (EQ_MP (@lem3459218 _89769 _89788 _89789 t P f) (@lem3459208 _89769 _89788 _89789 P f t)). Qed.
Lemma lem3459229 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3459230 {_89769 : Type'} (f : type1527 _89769) (y : Prop) : (term22 _89769 f y) = (f y).
Proof. exact (@lem3459229 Prop (type686 _89769) f y). Qed.
Lemma lem3459231 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89789) (y : _89788) : (term23 _89769 _89788 _89789 t P x y) = (term24 _89769 _89788 _89789 t P x y).
Proof. exact (@lem3459230 _89769 (term25 _89769 t) (P x y)). Qed.
Lemma lem3459232 {_89769 : Type'} (p : Prop) (t : _89769 -> Prop) : (term26 _89769 t p) = (term27 _89769 p t).
Proof. exact (eq_refl (term26 _89769 t p)). Qed.
Lemma lem3459233 {_89769 : Type'} (t : _89769 -> Prop) : (term28 _89769 t) = (term25 _89769 t).
Proof. exact (fun_ext (fun p : Prop => @lem3459232 _89769 p t)). Qed.
Lemma lem3459234 {_89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89789) (y : _89788) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3459235 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89789) (y : _89788) : (term23 _89769 _89788 _89789 t P x y) = (term24 _89769 _89788 _89789 t P x y).
Proof. exact (MK_COMB (@lem3459233 _89769 t) (@lem3459234 _89788 _89789 P x y)). Qed.
Lemma lem3459236 {_89769 : Type'} : (@eq ((_89769 -> Prop) -> Prop)) = (@eq ((_89769 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_89769 -> Prop) -> Prop))). Qed.
Lemma lem3459237 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89789) (y : _89788) : (term29 _89769 _89788 _89789 t P x y) = (term30 _89769 _89788 _89789 t P x y).
Proof. exact (MK_COMB (@lem3459236 _89769) (@lem3459235 _89769 _89788 _89789 t P x y)). Qed.
Lemma lem3459238 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89789) (y : _89788) (t : _89769 -> Prop) : (term24 _89769 _89788 _89789 t P x y) = (term31 _89769 _89788 _89789 P x y t).
Proof. exact (eq_refl (term24 _89769 _89788 _89789 t P x y)). Qed.
Lemma lem3459239 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89789) (y : _89788) (t : _89769 -> Prop) : ((term23 _89769 _89788 _89789 t P x y) = (term24 _89769 _89788 _89789 t P x y)) = ((term24 _89769 _89788 _89789 t P x y) = (term31 _89769 _89788 _89789 P x y t)).
Proof. exact (MK_COMB (@lem3459237 _89769 _89788 _89789 t P x y) (@lem3459238 _89769 _89788 _89789 P x y t)). Qed.
Lemma lem3459240 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89789) (y : _89788) (t : _89769 -> Prop) : (term24 _89769 _89788 _89789 t P x y) = (term31 _89769 _89788 _89789 P x y t).
Proof. exact (EQ_MP (@lem3459239 _89769 _89788 _89789 P x y t) (@lem3459231 _89769 _89788 _89789 t P x y)). Qed.
Lemma lem3459245 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (f x y) = (f x y).
Proof. exact (eq_refl (f x y)). Qed.
Lemma lem3459246 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term32 _89769 _89788 _89789 t P f x y) = (term33 _89769 _89788 _89789 P t f x y).
Proof. exact (MK_COMB (@lem3459240 _89769 _89788 _89789 P x y t) (@lem3459245 _89769 _89788 _89789 f x y)). Qed.
Lemma lem3459248 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3459249 {_89769 : Type'} (f : type686 _89769) (y : _89769 -> Prop) : (term34 _89769 f y) = (f y).
Proof. exact (@lem3459248 (_89769 -> Prop) Prop f y). Qed.
Lemma lem3459250 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term35 _89769 _89788 _89789 P t f x y) = (term33 _89769 _89788 _89789 P t f x y).
Proof. exact (@lem3459249 _89769 (term31 _89769 _89788 _89789 P x y t) (f x y)). Qed.
Lemma lem3459251 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89789) (y : _89788) (t : _89769 -> Prop) (t' : _89769 -> Prop) : (term36 _89769 _89788 _89789 P x y t t') = (term37 _89769 _89788 _89789 P x y t t').
Proof. exact (eq_refl (term36 _89769 _89788 _89789 P x y t t')). Qed.
Lemma lem3459252 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89789) (y : _89788) (t : _89769 -> Prop) : (term38 _89769 _89788 _89789 P x y t) = (term31 _89769 _89788 _89789 P x y t).
Proof. exact (fun_ext (fun t' : _89769 -> Prop => @lem3459251 _89769 _89788 _89789 P x y t t')). Qed.
Lemma lem3459253 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (f x y) = (f x y).
Proof. exact (eq_refl (f x y)). Qed.
Lemma lem3459254 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term35 _89769 _89788 _89789 P t f x y) = (term33 _89769 _89788 _89789 P t f x y).
Proof. exact (MK_COMB (@lem3459252 _89769 _89788 _89789 P x y t) (@lem3459253 _89769 _89788 _89789 f x y)). Qed.
Lemma lem3459255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459256 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term39 _89769 _89788 _89789 P t f x y) = (term40 _89769 _89788 _89789 P t f x y).
Proof. exact (MK_COMB (@lem3459255) (@lem3459254 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3459257 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term33 _89769 _89788 _89789 P t f x y) = (term41 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term33 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3459258 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : ((term35 _89769 _89788 _89789 P t f x y) = (term33 _89769 _89788 _89789 P t f x y)) = ((term33 _89769 _89788 _89789 P t f x y) = (term41 _89769 _89788 _89789 P t f x y)).
Proof. exact (MK_COMB (@lem3459256 _89769 _89788 _89789 P t f x y) (@lem3459257 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3459259 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term33 _89769 _89788 _89789 P t f x y) = (term41 _89769 _89788 _89789 P t f x y).
Proof. exact (EQ_MP (@lem3459258 _89769 _89788 _89789 P t f x y) (@lem3459250 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3459264 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term32 _89769 _89788 _89789 t P f x y) = (term41 _89769 _89788 _89789 P t f x y).
Proof. exact (TRANS (@lem3459246 _89769 _89788 _89789 P t f x y) (@lem3459259 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3459265 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term42 _89769 _89788 _89789 t P f x) = (term43 _89769 _89788 _89789 P t f x).
Proof. exact (fun_ext (fun y : _89788 => @lem3459264 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3459266 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3459267 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term44 _89769 _89788 _89789 t P f x) = (term45 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3459266 _89788) (@lem3459265 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3459272 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term46 _89769 _89788 _89789 t P f) = (term47 _89769 _89788 _89789 P t f).
Proof. exact (fun_ext (fun x : _89789 => @lem3459267 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3459273 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3459274 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term20 _89769 _89788 _89789 t P f) = (term48 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3459273 _89789) (@lem3459272 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3459279 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term17 _89769 _89788 _89789 t P f) = (term48 _89769 _89788 _89789 P t f).
Proof. exact (TRANS (@lem3459219 _89769 _89788 _89789 t P f) (@lem3459274 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3459280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3459281 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term49 _89769 _89788 _89789 t P f) = (term50 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3459280) (@lem3459279 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3459282 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (@IN _89769 x t) = (@IN _89769 x t).
Proof. exact (eq_refl (@IN _89769 x t)). Qed.
Lemma lem3459283 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term51 _89769 _89788 _89789 P f x t) = (term52 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3459281 _89769 _89788 _89789 P t f) (@lem3459282 _89769 x t)). Qed.
Lemma lem3459286 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term53 _89769 _89788 _89789 P f x) = (term54 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3459283 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3459287 {_89769 : Type'} : (@all (_89769 -> Prop)) = (@all (_89769 -> Prop)).
Proof. exact (eq_refl (@all (_89769 -> Prop))). Qed.
Lemma lem3459288 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term3 _89769 _89788 _89789 P f x) = (term55 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3459287 _89769) (@lem3459286 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3459293 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term2 _89769 _89788 _89789 x P f) = (term55 _89769 _89788 _89789 P f x).
Proof. exact (TRANS (@lem3459198 _89769 _89788 _89789 P f x) (@lem3459288 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3459294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459295 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term56 _89769 _89788 _89789 x P f) = (term57 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3459294) (@lem3459293 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3459297 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term58 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3459016 _83095 p x) (@lem3459015 _83095 p x)). Qed.
Lemma lem3459298 {_89769 : Type'} (p : _89769 -> Prop) (x : _89769) : (term58 _89769 x p) = (p x).
Proof. exact (@lem3459297 _89769 p x). Qed.
Lemma lem3459299 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term59 _89769 _89788 _89789 x P f) = (term60 _89769 _89788 _89789 P f x).
Proof. exact (@lem3459298 _89769 (term61 _89769 _89788 _89789 P f) x). Qed.
Lemma lem3459300 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (a : _89769) (f : type1517 _89769 _89788 _89789) : (term60 _89769 _89788 _89789 P f a) = (term62 _89769 _89788 _89789 P a f).
Proof. exact (eq_refl (term60 _89769 _89788 _89789 P f a)). Qed.
Lemma lem3459301 {_89769 : Type'} (GEN_PVAR_58 : _89769) : (@SETSPEC _89769 GEN_PVAR_58) = (@SETSPEC _89769 GEN_PVAR_58).
Proof. exact (eq_refl (@SETSPEC _89769 GEN_PVAR_58)). Qed.
Lemma lem3459302 {_89769 _89788 _89789 : Type'} (GEN_PVAR_58 : _89769) (P : type1470 _89788 _89789) (a : _89769) (f : type1517 _89769 _89788 _89789) : (term63 _89769 _89788 _89789 GEN_PVAR_58 P f a) = (term64 _89769 _89788 _89789 GEN_PVAR_58 P a f).
Proof. exact (MK_COMB (@lem3459301 _89769 GEN_PVAR_58) (@lem3459300 _89769 _89788 _89789 P a f)). Qed.
Lemma lem3459303 {_89769 : Type'} (a : _89769) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3459304 {_89769 _89788 _89789 : Type'} (GEN_PVAR_58 : _89769) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (a : _89769) : (term65 _89769 _89788 _89789 GEN_PVAR_58 P f a) = (term66 _89769 _89788 _89789 GEN_PVAR_58 P f a).
Proof. exact (MK_COMB (@lem3459302 _89769 _89788 _89789 GEN_PVAR_58 P a f) (@lem3459303 _89769 a)). Qed.
Lemma lem3459305 {_89769 _89788 _89789 : Type'} (GEN_PVAR_58 : _89769) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term67 _89769 _89788 _89789 GEN_PVAR_58 P f) = (term68 _89769 _89788 _89789 GEN_PVAR_58 P f).
Proof. exact (fun_ext (fun a : _89769 => @lem3459304 _89769 _89788 _89789 GEN_PVAR_58 P f a)). Qed.
Lemma lem3459306 {_89769 : Type'} : (@ex _89769) = (@ex _89769).
Proof. exact (eq_refl (@ex _89769)). Qed.
Lemma lem3459307 {_89769 _89788 _89789 : Type'} (GEN_PVAR_58 : _89769) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term69 _89769 _89788 _89789 GEN_PVAR_58 P f) = (term70 _89769 _89788 _89789 GEN_PVAR_58 P f).
Proof. exact (MK_COMB (@lem3459306 _89769) (@lem3459305 _89769 _89788 _89789 GEN_PVAR_58 P f)). Qed.
Lemma lem3459308 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term71 _89769 _89788 _89789 P f) = (term72 _89769 _89788 _89789 P f).
Proof. exact (fun_ext (fun GEN_PVAR_58 : _89769 => @lem3459307 _89769 _89788 _89789 GEN_PVAR_58 P f)). Qed.
Lemma lem3459309 {_89769 : Type'} : (@GSPEC _89769) = (@GSPEC _89769).
Proof. exact (eq_refl (@GSPEC _89769)). Qed.
Lemma lem3459310 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term73 _89769 _89788 _89789 P f) = (term74 _89769 _89788 _89789 P f).
Proof. exact (MK_COMB (@lem3459309 _89769) (@lem3459308 _89769 _89788 _89789 P f)). Qed.
Lemma lem3459311 {_89769 : Type'} (x : _89769) : (@IN _89769 x) = (@IN _89769 x).
Proof. exact (eq_refl (@IN _89769 x)). Qed.
Lemma lem3459312 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term59 _89769 _89788 _89789 x P f) = (term75 _89769 _89788 _89789 x P f).
Proof. exact (MK_COMB (@lem3459311 _89769 x) (@lem3459310 _89769 _89788 _89789 P f)). Qed.
Lemma lem3459313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459314 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term76 _89769 _89788 _89789 x P f) = (term77 _89769 _89788 _89789 x P f).
Proof. exact (MK_COMB (@lem3459313) (@lem3459312 _89769 _89788 _89789 x P f)). Qed.
Lemma lem3459315 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term60 _89769 _89788 _89789 P f x) = (term62 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term60 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3459316 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : ((term59 _89769 _89788 _89789 x P f) = (term60 _89769 _89788 _89789 P f x)) = ((term75 _89769 _89788 _89789 x P f) = (term62 _89769 _89788 _89789 P x f)).
Proof. exact (MK_COMB (@lem3459314 _89769 _89788 _89789 x P f) (@lem3459315 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3459317 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term75 _89769 _89788 _89789 x P f) = (term62 _89769 _89788 _89789 P x f).
Proof. exact (EQ_MP (@lem3459316 _89769 _89788 _89789 P x f) (@lem3459299 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3459328 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : ((term2 _89769 _89788 _89789 x P f) = (term75 _89769 _89788 _89789 x P f)) = ((term55 _89769 _89788 _89789 P f x) = (term62 _89769 _89788 _89789 P x f)).
Proof. exact (MK_COMB (@lem3459295 _89769 _89788 _89789 P f x) (@lem3459317 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3459331 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term78 _89769 _89788 _89789 P f) = (term79 _89769 _89788 _89789 P f).
Proof. exact (fun_ext (fun x : _89769 => @lem3459328 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3459332 {_89769 : Type'} : (@all _89769) = (@all _89769).
Proof. exact (eq_refl (@all _89769)). Qed.
Lemma lem3459333 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term80 _89769 _89788 _89789 P f) = (term81 _89769 _89788 _89789 P f).
Proof. exact (MK_COMB (@lem3459332 _89769) (@lem3459331 _89769 _89788 _89789 P f)). Qed.
Lemma lem3459338 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term81 _89769 _89788 _89789 P f) = (term80 _89769 _89788 _89789 P f).
Proof. exact (SYM (@lem3459333 _89769 _89788 _89789 P f)). Qed.
