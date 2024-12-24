Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_LE_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import LE_ADD2_spec.
Require Import LE_REFL_spec.
Require Import NSUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem6932171 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem6932172 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem6932173 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem6932172 A x) (@lem6932171 A x)). Qed.
Lemma lem6932174 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem6932173 A x y). Qed.
Lemma lem6932175 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem6932176 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem6932175 A y x) (@lem6932174 A x y)). Qed.
Lemma lem6932177 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term4 A y x s.
Proof. exact (@lem6932176 A y x s). Qed.
Lemma lem6932178 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A y x s) = ((term5 A x y s) = (term6 A y x s)).
Proof. exact (eq_refl (term4 A y x s)). Qed.
Lemma lem6932180 (m : nat) : term7 m.
Proof. exact (@lem101399 m). Qed.
Lemma lem6932181 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem6932182 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem6932181 m) (@lem6932180 m)). Qed.
Lemma lem6932183 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem6932182 m n). Qed.
Lemma lem6932184 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem6932185 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem6932184 m n) (@lem6932183 m n)). Qed.
Lemma lem6932186 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem6932185 m n p). Qed.
Lemma lem6932187 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term12 m n p).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem6932188 (m : nat) (n : nat) (p : nat) : term12 m n p.
Proof. exact (EQ_MP (@lem6932187 m n p) (@lem6932186 m n p)). Qed.
Lemma lem6932189 (m : nat) (n : nat) (p : nat) (q : nat) : term13 m n p q.
Proof. exact (@lem6932188 m n p q). Qed.
Lemma lem6932190 (m : nat) (n : nat) (p : nat) (q : nat) : (term13 m n p q) = (term14 m n p q).
Proof. exact (eq_refl (term13 m n p q)). Qed.
Lemma lem6932191 (m : nat) (n : nat) (p : nat) (q : nat) : term14 m n p q.
Proof. exact (EQ_MP (@lem6932190 m n p q) (@lem6932189 m n p q)). Qed.
Lemma lem6932192 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term15 m p n q) : term15 m p n q.
Proof. exact (h1). Qed.
Lemma lem6932193 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term15 m p n q) : term16 m n p q.
Proof. exact (@lem6932191 m n p q (@lem6932192 m p n q h1)). Qed.
Lemma lem6932194 (m : nat) (n : nat) (p : nat) (q : nat) : (term16 m n p q) = ((term16 m n p q) = True).
Proof. exact (@lem7 (term16 m n p q)). Qed.
Lemma lem6932195 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term15 m p n q) : (term16 m n p q) = True.
Proof. exact (EQ_MP (@lem6932194 m n p q) (@lem6932193 m p n q h1)). Qed.
Lemma lem6932201 (n : nat) : term17 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem6932202 (n : nat) : (term17 n) = (Peano.le n n).
Proof. exact (eq_refl (term17 n)). Qed.
Lemma lem6932203 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem6932202 n) (@lem6932201 n)). Qed.
Lemma lem6932204 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem6932206 {_126525 : Type'} : term18 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem6932207 {_126525 : Type'} (x : _126525) : term19 _126525 x.
Proof. exact (@lem6932206 _126525 x). Qed.
Lemma lem6932208 {_126525 : Type'} (x : _126525) : (term19 _126525 x) = (term20 _126525 x).
Proof. exact (eq_refl (term19 _126525 x)). Qed.
Lemma lem6932209 {_126525 : Type'} (x : _126525) : term20 _126525 x.
Proof. exact (EQ_MP (@lem6932208 _126525 x) (@lem6932207 _126525 x)). Qed.
Lemma lem6932210 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term21 _126525 x f.
Proof. exact (@lem6932209 _126525 x f). Qed.
Lemma lem6932211 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term21 _126525 x f) = (term22 _126525 x f).
Proof. exact (eq_refl (term21 _126525 x f)). Qed.
Lemma lem6932212 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term22 _126525 x f.
Proof. exact (EQ_MP (@lem6932211 _126525 x f) (@lem6932210 _126525 x f)). Qed.
Lemma lem6932213 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term23 _126525 x f s.
Proof. exact (@lem6932212 _126525 x f s). Qed.
Lemma lem6932214 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term23 _126525 x f s) = (term24 _126525 x s f).
Proof. exact (eq_refl (term23 _126525 x f s)). Qed.
Lemma lem6932215 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term24 _126525 x s f.
Proof. exact (EQ_MP (@lem6932214 _126525 x s f) (@lem6932213 _126525 x f s)). Qed.
Lemma lem6932216 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem6932217 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term25 _126525 x s f) = (term26 _126525 x s f).
Proof. exact (@lem6932215 _126525 x s f (@lem6932216 _126525 s h1)). Qed.
Lemma lem6932223 {_126486 : Type'} : term27 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem6932224 {_126486 : Type'} (f : _126486 -> nat) : term28 _126486 f.
Proof. exact (@lem6932223 _126486 f). Qed.
Lemma lem6932225 {_126486 : Type'} (f : _126486 -> nat) : (term28 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term28 _126486 f)). Qed.
Lemma lem6932227 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem6932228 {A : Type'} (P : type686 A) (h1 : term29 A) : term30 A P.
Proof. exact (@lem6932227 A h1 P). Qed.
Lemma lem6932229 {A : Type'} (P : type686 A) : (term30 A P) = (term31 A P).
Proof. exact (eq_refl (term30 A P)). Qed.
Lemma lem6932230 {A : Type'} (P : type686 A) (h1 : term29 A) : term31 A P.
Proof. exact (EQ_MP (@lem6932229 A P) (@lem6932228 A P h1)). Qed.
Lemma lem6932231 {A : Type'} (P : type686 A) (h1 : term32 A P) : term32 A P.
Proof. exact (h1). Qed.
Lemma lem6932232 {A : Type'} (P : type686 A) (h1 : term29 A) (h2 : term32 A P) : term33 A P.
Proof. exact (@lem6932230 A P h1 (@lem6932231 A P h2)). Qed.
Lemma lem6932233 {A : Type'} (P : type686 A) (h1 : term32 A P) : term34 A P.
Proof. exact (fun h0 : term29 A => @lem6932232 A P h0 h1). Qed.
Lemma lem6932234 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem6932235 {A : Type'} (P : type686 A) (h1 : term29 A) (h2 : term32 A P) : term33 A P.
Proof. exact (@lem6932233 A P h2 (@lem6932234 A h1)). Qed.
Lemma lem6932236 {A : Type'} (P : type686 A) (h1 : term29 A) : term31 A P.
Proof. exact (fun h0 : term32 A P => @lem6932235 A P h1 h0). Qed.
Lemma lem6932237 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (fun P : type686 A => @lem6932236 A P h1). Qed.
Lemma lem6932238 {A : Type'} : term35 A.
Proof. exact (fun h0 : term29 A => @lem6932237 A h0). Qed.
Lemma lem6932239 {A : Type'} : term29 A.
Proof. exact (@lem6932238 A (@lem3558722 A)). Qed.
Lemma lem6932240 {A : Type'} (P : type686 A) : term30 A P.
Proof. exact (@lem6932239 A P). Qed.
Lemma lem6932241 {A : Type'} (P : type686 A) : (term30 A P) = (term31 A P).
Proof. exact (eq_refl (term30 A P)). Qed.
Lemma lem6932256 (p : Prop) (q : Prop) (r : Prop) : (term36 p q r) = (term37 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem6932257 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term38 _127006 f s g) = (term39 _127006 f s g).
Proof. exact (@lem6932256 (@FINITE _127006 s) (term40 _127006 s f g) (term41 _127006 f s g)). Qed.
Lemma lem6932258 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term42 _127006 f g) = (term43 _127006 f g).
Proof. exact (fun_ext (fun s : _127006 -> Prop => @lem6932257 _127006 f s g)). Qed.
Lemma lem6932259 {_127006 : Type'} : (@all (_127006 -> Prop)) = (@all (_127006 -> Prop)).
Proof. exact (eq_refl (@all (_127006 -> Prop))). Qed.
Lemma lem6932260 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term44 _127006 f g) = (term45 _127006 f g).
Proof. exact (MK_COMB (@lem6932259 _127006) (@lem6932258 _127006 f g)). Qed.
Lemma lem6932261 {_127006 : Type'} (f : _127006 -> nat) : (term46 _127006 f) = (term47 _127006 f).
Proof. exact (fun_ext (fun g : _127006 -> nat => @lem6932260 _127006 f g)). Qed.
Lemma lem6932262 {_127006 : Type'} : (@all (_127006 -> nat)) = (@all (_127006 -> nat)).
Proof. exact (eq_refl (@all (_127006 -> nat))). Qed.
Lemma lem6932263 {_127006 : Type'} (f : _127006 -> nat) : (term48 _127006 f) = (term49 _127006 f).
Proof. exact (MK_COMB (@lem6932262 _127006) (@lem6932261 _127006 f)). Qed.
Lemma lem6932264 {_127006 : Type'} : (term50 _127006) = (term51 _127006).
Proof. exact (fun_ext (fun f : _127006 -> nat => @lem6932263 _127006 f)). Qed.
Lemma lem6932265 {_127006 : Type'} : (@all (_127006 -> nat)) = (@all (_127006 -> nat)).
Proof. exact (eq_refl (@all (_127006 -> nat))). Qed.
Lemma lem6932266 {_127006 : Type'} : (term52 _127006) = (term53 _127006).
Proof. exact (MK_COMB (@lem6932265 _127006) (@lem6932264 _127006)). Qed.
Lemma lem6932267 {_127006 : Type'} : (term53 _127006) = (term52 _127006).
Proof. exact (SYM (@lem6932266 _127006)). Qed.
Lemma lem6932269 {A : Type'} (P : type686 A) : term31 A P.
Proof. exact (EQ_MP (@lem6932241 A P) (@lem6932240 A P)). Qed.
Lemma lem6932270 {_127006 : Type'} (P : type686 _127006) : term31 _127006 P.
Proof. exact (@lem6932269 _127006 P). Qed.
Lemma lem6932271 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term54 _127006 f g.
Proof. exact (@lem6932270 _127006 (term55 _127006 f g)). Qed.
Lemma lem6932272 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term56 _127006 f g) = (term57 _127006 f g).
Proof. exact (eq_refl (term56 _127006 f g)). Qed.
Lemma lem6932273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6932274 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term58 _127006 f g) = (term59 _127006 f g).
Proof. exact (MK_COMB (@lem6932273) (@lem6932272 _127006 f g)). Qed.
Lemma lem6932275 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term60 _127006 f g s) = (term61 _127006 f s g).
Proof. exact (eq_refl (term60 _127006 f g s)). Qed.
Lemma lem6932276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6932277 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term62 _127006 f g s) = (term63 _127006 f s g).
Proof. exact (MK_COMB (@lem6932276) (@lem6932275 _127006 f s g)). Qed.
Lemma lem6932278 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) : (term64 _127006 x s) = (term64 _127006 x s).
Proof. exact (eq_refl (term64 _127006 x s)). Qed.
Lemma lem6932279 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) : (term65 _127006 f g x s) = (term66 _127006 f g x s).
Proof. exact (MK_COMB (@lem6932277 _127006 f s g) (@lem6932278 _127006 x s)). Qed.
Lemma lem6932280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6932281 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) : (term67 _127006 f g x s) = (term68 _127006 f g x s).
Proof. exact (MK_COMB (@lem6932280) (@lem6932279 _127006 f g x s)). Qed.
Lemma lem6932282 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : (term69 _127006 f g x s) = (term70 _127006 f x s g).
Proof. exact (eq_refl (term69 _127006 f g x s)). Qed.
Lemma lem6932283 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : (term71 _127006 f g x s) = (term72 _127006 f x s g).
Proof. exact (MK_COMB (@lem6932281 _127006 f g x s) (@lem6932282 _127006 f x s g)). Qed.
Lemma lem6932284 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (g : _127006 -> nat) : (term73 _127006 f g x) = (term74 _127006 f x g).
Proof. exact (fun_ext (fun s : _127006 -> Prop => @lem6932283 _127006 f x s g)). Qed.
Lemma lem6932285 {_127006 : Type'} : (@all (_127006 -> Prop)) = (@all (_127006 -> Prop)).
Proof. exact (eq_refl (@all (_127006 -> Prop))). Qed.
Lemma lem6932286 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (g : _127006 -> nat) : (term75 _127006 f g x) = (term76 _127006 f x g).
Proof. exact (MK_COMB (@lem6932285 _127006) (@lem6932284 _127006 f x g)). Qed.
Lemma lem6932287 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term77 _127006 f g) = (term78 _127006 f g).
Proof. exact (fun_ext (fun x : _127006 => @lem6932286 _127006 f x g)). Qed.
Lemma lem6932288 {_127006 : Type'} : (@all _127006) = (@all _127006).
Proof. exact (eq_refl (@all _127006)). Qed.
Lemma lem6932289 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term79 _127006 f g) = (term80 _127006 f g).
Proof. exact (MK_COMB (@lem6932288 _127006) (@lem6932287 _127006 f g)). Qed.
Lemma lem6932290 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term81 _127006 f g) = (term82 _127006 f g).
Proof. exact (MK_COMB (@lem6932274 _127006 f g) (@lem6932289 _127006 f g)). Qed.
Lemma lem6932291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6932292 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term83 _127006 f g) = (term84 _127006 f g).
Proof. exact (MK_COMB (@lem6932291) (@lem6932290 _127006 f g)). Qed.
Lemma lem6932293 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term60 _127006 f g s) = (term61 _127006 f s g).
Proof. exact (eq_refl (term60 _127006 f g s)). Qed.
Lemma lem6932294 {_127006 : Type'} (s : _127006 -> Prop) : (term85 _127006 s) = (term85 _127006 s).
Proof. exact (eq_refl (term85 _127006 s)). Qed.
Lemma lem6932295 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term86 _127006 f g s) = (term39 _127006 f s g).
Proof. exact (MK_COMB (@lem6932294 _127006 s) (@lem6932293 _127006 f s g)). Qed.
Lemma lem6932296 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term87 _127006 f g) = (term43 _127006 f g).
Proof. exact (fun_ext (fun s : _127006 -> Prop => @lem6932295 _127006 f s g)). Qed.
Lemma lem6932297 {_127006 : Type'} : (@all (_127006 -> Prop)) = (@all (_127006 -> Prop)).
Proof. exact (eq_refl (@all (_127006 -> Prop))). Qed.
Lemma lem6932298 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term88 _127006 f g) = (term45 _127006 f g).
Proof. exact (MK_COMB (@lem6932297 _127006) (@lem6932296 _127006 f g)). Qed.
Lemma lem6932299 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term54 _127006 f g) = (term89 _127006 f g).
Proof. exact (MK_COMB (@lem6932292 _127006 f g) (@lem6932298 _127006 f g)). Qed.
Lemma lem6932300 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term89 _127006 f g.
Proof. exact (EQ_MP (@lem6932299 _127006 f g) (@lem6932271 _127006 f g)). Qed.
Lemma lem6932306 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6932307 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem6932306 p q p' q'). Qed.
Lemma lem6932308 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem6932307 p q p'). Qed.
Lemma lem6932309 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term93 _127006 f g.
Proof. exact (@lem6932308 (term94 _127006 f g) (term95 _127006 f g)). Qed.
Lemma lem6932310 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (p' : Prop) : term96 _127006 f g p'.
Proof. exact (@lem6932309 _127006 f g p'). Qed.
Lemma lem6932311 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (p' : Prop) : (term96 _127006 f g p') = (term97 _127006 f g p').
Proof. exact (eq_refl (term96 _127006 f g p')). Qed.
Lemma lem6932312 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (p' : Prop) : term97 _127006 f g p'.
Proof. exact (EQ_MP (@lem6932311 _127006 f g p') (@lem6932310 _127006 f g p')). Qed.
Lemma lem6932313 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : term98 _127006 f g p' q'.
Proof. exact (@lem6932312 _127006 f g p' q'). Qed.
Lemma lem6932314 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : (term98 _127006 f g p' q') = (term99 _127006 f g p' q').
Proof. exact (eq_refl (term98 _127006 f g p' q')). Qed.
Lemma lem6932315 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : term99 _127006 f g p' q'.
Proof. exact (EQ_MP (@lem6932314 _127006 f g p' q') (@lem6932313 _127006 f g p' q')). Qed.
Lemma lem6932347 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term94 _127006 f g) = (term94 _127006 f g).
Proof. exact (eq_refl (term94 _127006 f g)). Qed.
Lemma lem6932348 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (q' : Prop) : term100 _127006 f g q'.
Proof. exact (@lem6932315 _127006 f g (term94 _127006 f g) q'). Qed.
Lemma lem6932349 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (q' : Prop) : term101 _127006 f g q'.
Proof. exact (@lem6932348 _127006 f g q' (@lem6932347 _127006 f g)). Qed.
Lemma lem6932366 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6932225 _126486 f) (@lem6932224 _126486 f)). Qed.
Lemma lem6932367 {_127006 : Type'} (f : _127006 -> nat) : (@nsum _127006 (@EMPTY _127006) f) = (NUMERAL 0).
Proof. exact (@lem6932366 _127006 f). Qed.
Lemma lem6932368 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6932369 {_127006 : Type'} (f : _127006 -> nat) : (term102 _127006 f) = term103.
Proof. exact (MK_COMB (@lem6932368) (@lem6932367 _127006 f)). Qed.
Lemma lem6932371 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6932225 _126486 f) (@lem6932224 _126486 f)). Qed.
Lemma lem6932372 {_127006 : Type'} (f : _127006 -> nat) : (@nsum _127006 (@EMPTY _127006) f) = (NUMERAL 0).
Proof. exact (@lem6932371 _127006 f). Qed.
Lemma lem6932373 {_127006 : Type'} (g : _127006 -> nat) : (@nsum _127006 (@EMPTY _127006) g) = (NUMERAL 0).
Proof. exact (@lem6932372 _127006 g). Qed.
Lemma lem6932374 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term95 _127006 f g) = term104.
Proof. exact (MK_COMB (@lem6932369 _127006 f) (@lem6932373 _127006 g)). Qed.
Lemma lem6932376 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem6932204 n) (@lem6932203 n)). Qed.
Lemma lem6932377 : term104 = True.
Proof. exact (@lem6932376 (NUMERAL 0)). Qed.
Lemma lem6932378 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term95 _127006 f g) = True.
Proof. exact (TRANS (@lem6932374 _127006 f g) (@lem6932377)). Qed.
Lemma lem6932379 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term105 _127006 f g.
Proof. exact (fun h0 : term94 _127006 f g => @lem6932378 _127006 f g). Qed.
Lemma lem6932380 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term106 _127006 f g.
Proof. exact (@lem6932349 _127006 f g True). Qed.
Lemma lem6932381 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term57 _127006 f g) = (term107 _127006 f g).
Proof. exact (@lem6932380 _127006 f g (@lem6932379 _127006 f g)). Qed.
Lemma lem6932383 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6932384 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term107 _127006 f g) = True.
Proof. exact (@lem6932383 (term94 _127006 f g)). Qed.
Lemma lem6932385 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term57 _127006 f g) = True.
Proof. exact (TRANS (@lem6932381 _127006 f g) (@lem6932384 _127006 f g)). Qed.
Lemma lem6932386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6932387 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term59 _127006 f g) = (and True).
Proof. exact (MK_COMB (@lem6932386) (@lem6932385 _127006 f g)). Qed.
Lemma lem6932399 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6932400 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem6932399 p q p' q'). Qed.
Lemma lem6932401 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem6932400 p q p'). Qed.
Lemma lem6932402 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : term108 _127006 f x s g.
Proof. exact (@lem6932401 (term66 _127006 f g x s) (term70 _127006 f x s g)). Qed.
Lemma lem6932403 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) : term109 _127006 f x s g p'.
Proof. exact (@lem6932402 _127006 f x s g p'). Qed.
Lemma lem6932404 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) : (term109 _127006 f x s g p') = (term110 _127006 f x s g p').
Proof. exact (eq_refl (term109 _127006 f x s g p')). Qed.
Lemma lem6932405 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) : term110 _127006 f x s g p'.
Proof. exact (EQ_MP (@lem6932404 _127006 f x s g p') (@lem6932403 _127006 f x s g p')). Qed.
Lemma lem6932406 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : term111 _127006 f x s g p' q'.
Proof. exact (@lem6932405 _127006 f x s g p' q'). Qed.
Lemma lem6932407 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : (term111 _127006 f x s g p' q') = (term112 _127006 f x s g p' q').
Proof. exact (eq_refl (term111 _127006 f x s g p' q')). Qed.
Lemma lem6932408 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : term112 _127006 f x s g p' q'.
Proof. exact (EQ_MP (@lem6932407 _127006 f x s g p' q') (@lem6932406 _127006 f x s g p' q')). Qed.
Lemma lem6932512 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) : (term66 _127006 f g x s) = (term66 _127006 f g x s).
Proof. exact (eq_refl (term66 _127006 f g x s)). Qed.
Lemma lem6932513 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (q' : Prop) : term113 _127006 f g x s q'.
Proof. exact (@lem6932408 _127006 f x s g (term66 _127006 f g x s) q'). Qed.
Lemma lem6932514 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (q' : Prop) : term114 _127006 f g x s q'.
Proof. exact (@lem6932513 _127006 f g x s q' (@lem6932512 _127006 f g x s)). Qed.
Lemma lem6932515 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term66 _127006 f g x s.
Proof. exact (h1). Qed.
Lemma lem6932516 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term64 _127006 x s.
Proof. exact (proj2 (@lem6932515 _127006 f g x s h1)). Qed.
Lemma lem6932517 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : @FINITE _127006 s.
Proof. exact (proj2 (@lem6932516 _127006 f g x s h1)). Qed.
Lemma lem6932518 {_127006 : Type'} (s : _127006 -> Prop) : (@FINITE _127006 s) = ((@FINITE _127006 s) = True).
Proof. exact (@lem7 (@FINITE _127006 s)). Qed.
Lemma lem6932520 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term115 _127006 x s.
Proof. exact (proj1 (@lem6932516 _127006 f g x s h1)). Qed.
Lemma lem6932521 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) : term116 _127006 x s.
Proof. exact (@lem82 (@IN _127006 x s)). Qed.
Lemma lem6932523 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term61 _127006 f s g.
Proof. exact (proj1 (@lem6932515 _127006 f g x s h1)). Qed.
Lemma lem6932524 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term40 _127006 s f g) : term40 _127006 s f g.
Proof. exact (h1). Qed.
Lemma lem6932525 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term40 _127006 s f g) (h2 : term66 _127006 f g x s) : term41 _127006 f s g.
Proof. exact (@lem6932523 _127006 f g x s h2 (@lem6932524 _127006 s f g h1)). Qed.
Lemma lem6932526 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term41 _127006 f s g) = ((term41 _127006 f s g) = True).
Proof. exact (@lem7 (term41 _127006 f s g)). Qed.
Lemma lem6932527 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term40 _127006 s f g) (h2 : term66 _127006 f g x s) : (term41 _127006 f s g) = True.
Proof. exact (EQ_MP (@lem6932526 _127006 f s g) (@lem6932525 _127006 f g x s h1 h2)). Qed.
Lemma lem6932536 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6932537 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem6932536 p q p' q'). Qed.
Lemma lem6932538 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem6932537 p q p'). Qed.
Lemma lem6932539 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : term117 _127006 f x s g.
Proof. exact (@lem6932538 (term118 _127006 x s f g) (term119 _127006 f x s g)). Qed.
Lemma lem6932540 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) : term120 _127006 f x s g p'.
Proof. exact (@lem6932539 _127006 f x s g p'). Qed.
Lemma lem6932541 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) : (term120 _127006 f x s g p') = (term121 _127006 f x s g p').
Proof. exact (eq_refl (term120 _127006 f x s g p')). Qed.
Lemma lem6932542 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) : term121 _127006 f x s g p'.
Proof. exact (EQ_MP (@lem6932541 _127006 f x s g p') (@lem6932540 _127006 f x s g p')). Qed.
Lemma lem6932543 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : term122 _127006 f x s g p' q'.
Proof. exact (@lem6932542 _127006 f x s g p' q'). Qed.
Lemma lem6932544 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : (term122 _127006 f x s g p' q') = (term123 _127006 f x s g p' q').
Proof. exact (eq_refl (term122 _127006 f x s g p' q')). Qed.
Lemma lem6932545 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (p' : Prop) (q' : Prop) : term123 _127006 f x s g p' q'.
Proof. exact (EQ_MP (@lem6932544 _127006 f x s g p' q') (@lem6932543 _127006 f x s g p' q')). Qed.
Lemma lem6932553 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6932554 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem6932553 p q p' q'). Qed.
Lemma lem6932555 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem6932554 p q p'). Qed.
Lemma lem6932556 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) : term124 _127006 x s f g x'.
Proof. exact (@lem6932555 (term5 _127006 x' x s) (term125 _127006 f g x')). Qed.
Lemma lem6932557 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) (p' : Prop) : term126 _127006 x s f g x' p'.
Proof. exact (@lem6932556 _127006 x s f g x' p'). Qed.
Lemma lem6932558 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) (p' : Prop) : (term126 _127006 x s f g x' p') = (term127 _127006 x s f g x' p').
Proof. exact (eq_refl (term126 _127006 x s f g x' p')). Qed.
Lemma lem6932559 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) (p' : Prop) : term127 _127006 x s f g x' p'.
Proof. exact (EQ_MP (@lem6932558 _127006 x s f g x' p') (@lem6932557 _127006 x s f g x' p')). Qed.
Lemma lem6932560 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) (p' : Prop) (q' : Prop) : term128 _127006 x s f g x' p' q'.
Proof. exact (@lem6932559 _127006 x s f g x' p' q'). Qed.
Lemma lem6932561 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) (p' : Prop) (q' : Prop) : (term128 _127006 x s f g x' p' q') = (term129 _127006 x s f g x' p' q').
Proof. exact (eq_refl (term128 _127006 x s f g x' p' q')). Qed.
Lemma lem6932562 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) (p' : Prop) (q' : Prop) : term129 _127006 x s f g x' p' q'.
Proof. exact (EQ_MP (@lem6932561 _127006 x s f g x' p' q') (@lem6932560 _127006 x s f g x' p' q')). Qed.
Lemma lem6932564 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem6932178 A y x s) (@lem6932177 A y x s)). Qed.
Lemma lem6932565 {_127006 : Type'} (y : _127006) (x : _127006) (s : _127006 -> Prop) : (term5 _127006 x y s) = (term6 _127006 y x s).
Proof. exact (@lem6932564 _127006 y x s). Qed.
Lemma lem6932566 {_127006 : Type'} (x : _127006) (x' : _127006) (s : _127006 -> Prop) : (term5 _127006 x' x s) = (term6 _127006 x x' s).
Proof. exact (@lem6932565 _127006 x x' s). Qed.
Lemma lem6932571 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (x' : _127006) (s : _127006 -> Prop) (q' : Prop) : term130 _127006 f g x x' s q'.
Proof. exact (@lem6932562 _127006 x s f g x' (term6 _127006 x x' s) q'). Qed.
Lemma lem6932572 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (x' : _127006) (s : _127006 -> Prop) (q' : Prop) : term131 _127006 f g x x' s q'.
Proof. exact (@lem6932571 _127006 f g x x' s q' (@lem6932566 _127006 x x' s)). Qed.
Lemma lem6932578 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) : (term125 _127006 f g x') = (term125 _127006 f g x').
Proof. exact (eq_refl (term125 _127006 f g x')). Qed.
Lemma lem6932579 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) : term132 _127006 x s f g x'.
Proof. exact (fun h0 : term6 _127006 x x' s => @lem6932578 _127006 f g x'). Qed.
Lemma lem6932580 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) : term133 _127006 x s f g x'.
Proof. exact (@lem6932572 _127006 f g x x' s (term125 _127006 f g x')). Qed.
Lemma lem6932581 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) : (term134 _127006 x s f g x') = (term135 _127006 x s f g x').
Proof. exact (@lem6932580 _127006 x s f g x' (@lem6932579 _127006 x s f g x')). Qed.
Lemma lem6932617 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) : (term136 _127006 x s f g) = (term137 _127006 x s f g).
Proof. exact (fun_ext (fun x' : _127006 => @lem6932581 _127006 x s f g x')). Qed.
Lemma lem6932653 {_127006 : Type'} : (@all _127006) = (@all _127006).
Proof. exact (eq_refl (@all _127006)). Qed.
Lemma lem6932654 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) : (term118 _127006 x s f g) = (term138 _127006 x s f g).
Proof. exact (MK_COMB (@lem6932653 _127006) (@lem6932617 _127006 x s f g)). Qed.
Lemma lem6932694 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (q' : Prop) : term139 _127006 x s f g q'.
Proof. exact (@lem6932545 _127006 f x s g (term138 _127006 x s f g) q'). Qed.
Lemma lem6932695 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (q' : Prop) : term140 _127006 x s f g q'.
Proof. exact (@lem6932694 _127006 x s f g q' (@lem6932654 _127006 x s f g)). Qed.
Lemma lem6932696 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term138 _127006 x s f g.
Proof. exact (h1). Qed.
Lemma lem6932697 {_127006 : Type'} (x' : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term141 _127006 x s f g x'.
Proof. exact (@lem6932696 _127006 x s f g h1 x'). Qed.
Lemma lem6932698 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) : (term141 _127006 x s f g x') = (term135 _127006 x s f g x').
Proof. exact (eq_refl (term141 _127006 x s f g x')). Qed.
Lemma lem6932699 {_127006 : Type'} (x' : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term135 _127006 x s f g x'.
Proof. exact (EQ_MP (@lem6932698 _127006 x s f g x') (@lem6932697 _127006 x' x s f g h1)). Qed.
Lemma lem6932700 {_127006 : Type'} (x : _127006) (x' : _127006) (s : _127006 -> Prop) (h1 : term6 _127006 x x' s) : term6 _127006 x x' s.
Proof. exact (h1). Qed.
Lemma lem6932701 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (x' : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term6 _127006 x x' s) : term125 _127006 f g x'.
Proof. exact (@lem6932699 _127006 x' x s f g h1 (@lem6932700 _127006 x x' s h2)). Qed.
Lemma lem6932702 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x' : _127006) : (term125 _127006 f g x') = ((term125 _127006 f g x') = True).
Proof. exact (@lem7 (term125 _127006 f g x')). Qed.
Lemma lem6932703 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (x' : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term6 _127006 x x' s) : (term125 _127006 f g x') = True.
Proof. exact (EQ_MP (@lem6932702 _127006 f g x') (@lem6932701 _127006 f g x x' s h1 h2)). Qed.
Lemma lem6932712 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term24 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6932217 _126525 x f s h0). Qed.
Lemma lem6932713 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) : term24 _127006 x s f.
Proof. exact (@lem6932712 _127006 x s f). Qed.
Lemma lem6932715 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (@FINITE _127006 s) = True.
Proof. exact (EQ_MP (@lem6932518 _127006 s) (@lem6932517 _127006 f g x s h1)). Qed.
Lemma lem6932716 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : True = (@FINITE _127006 s).
Proof. exact (SYM (@lem6932715 _127006 f g x s h1)). Qed.
Lemma lem6932717 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : @FINITE _127006 s.
Proof. exact (EQ_MP (@lem6932716 _127006 f g x s h1) (@lem0)). Qed.
Lemma lem6932718 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term25 _127006 x s f) = (term26 _127006 x s f).
Proof. exact (@lem6932713 _127006 x s f (@lem6932717 _127006 f g x s h1)). Qed.
Lemma lem6932720 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term142 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6932721 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term143 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6932720 _2963 g t e g' t' e'). Qed.
Lemma lem6932722 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term144 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6932721 _2963 g t e g' t'). Qed.
Lemma lem6932723 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term145 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6932722 _2963 g t e g'). Qed.
Lemma lem6932724 (g : Prop) (t : nat) (e : nat) : term146 g t e.
Proof. exact (@lem6932723 nat g t e). Qed.
Lemma lem6932725 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) : term147 _127006 x s f.
Proof. exact (@lem6932724 (@IN _127006 x s) (@nsum _127006 s f) (term148 _127006 x s f)). Qed.
Lemma lem6932726 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) : term149 _127006 x s f g'.
Proof. exact (@lem6932725 _127006 x s f g'). Qed.
Lemma lem6932727 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) : (term149 _127006 x s f g') = (term150 _127006 x s f g').
Proof. exact (eq_refl (term149 _127006 x s f g')). Qed.
Lemma lem6932728 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) : term150 _127006 x s f g'.
Proof. exact (EQ_MP (@lem6932727 _127006 x s f g') (@lem6932726 _127006 x s f g')). Qed.
Lemma lem6932729 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) (t' : nat) : term151 _127006 x s f g' t'.
Proof. exact (@lem6932728 _127006 x s f g' t'). Qed.
Lemma lem6932730 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) (t' : nat) : (term151 _127006 x s f g' t') = (term152 _127006 x s f g' t').
Proof. exact (eq_refl (term151 _127006 x s f g' t')). Qed.
Lemma lem6932731 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) (t' : nat) : term152 _127006 x s f g' t'.
Proof. exact (EQ_MP (@lem6932730 _127006 x s f g' t') (@lem6932729 _127006 x s f g' t')). Qed.
Lemma lem6932732 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) (t' : nat) (e' : nat) : term153 _127006 x s f g' t' e'.
Proof. exact (@lem6932731 _127006 x s f g' t' e'). Qed.
Lemma lem6932733 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term153 _127006 x s f g' t' e') = (term154 _127006 x s f g' t' e').
Proof. exact (eq_refl (term153 _127006 x s f g' t' e')). Qed.
Lemma lem6932734 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g' : Prop) (t' : nat) (e' : nat) : term154 _127006 x s f g' t' e'.
Proof. exact (EQ_MP (@lem6932733 _127006 x s f g' t' e') (@lem6932732 _127006 x s f g' t' e')). Qed.
Lemma lem6932736 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (@IN _127006 x s) = False.
Proof. exact (@lem6932521 _127006 x s (@lem6932520 _127006 f g x s h1)). Qed.
Lemma lem6932737 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (t' : nat) (e' : nat) : term155 _127006 x s f t' e'.
Proof. exact (@lem6932734 _127006 x s f False t' e'). Qed.
Lemma lem6932738 {_127006 : Type'} (t' : nat) (e' : nat) (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term156 _127006 x s f t' e'.
Proof. exact (@lem6932737 _127006 x s f t' e' (@lem6932736 _127006 f g x s h1)). Qed.
Lemma lem6932742 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) : (@nsum _127006 s f) = (@nsum _127006 s f).
Proof. exact (eq_refl (@nsum _127006 s f)). Qed.
Lemma lem6932743 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) : term157 _127006 s f.
Proof. exact (fun h0 : False => @lem6932742 _127006 s f). Qed.
Lemma lem6932744 {_127006 : Type'} (e' : nat) (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term158 _127006 x s f e'.
Proof. exact (@lem6932738 _127006 (@nsum _127006 s f) e' f g x s h1). Qed.
Lemma lem6932745 {_127006 : Type'} (e' : nat) (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term159 _127006 x s f e'.
Proof. exact (@lem6932744 _127006 e' f g x s h1 (@lem6932743 _127006 s f)). Qed.
Lemma lem6932751 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) : (term148 _127006 x s f) = (term148 _127006 x s f).
Proof. exact (eq_refl (term148 _127006 x s f)). Qed.
Lemma lem6932752 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) : term160 _127006 x s f.
Proof. exact (fun h0 : ~ False => @lem6932751 _127006 x s f). Qed.
Lemma lem6932753 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term161 _127006 x s f.
Proof. exact (@lem6932745 _127006 (term148 _127006 x s f) f g x s h1). Qed.
Lemma lem6932754 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term26 _127006 x s f) = (term162 _127006 x s f).
Proof. exact (@lem6932753 _127006 f g x s h1 (@lem6932752 _127006 x s f)). Qed.
Lemma lem6932756 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6932757 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6932756 nat t1 t2). Qed.
Lemma lem6932758 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) : (term162 _127006 x s f) = (term148 _127006 x s f).
Proof. exact (@lem6932757 (@nsum _127006 s f) (term148 _127006 x s f)). Qed.
Lemma lem6932759 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term26 _127006 x s f) = (term148 _127006 x s f).
Proof. exact (TRANS (@lem6932754 _127006 f g x s h1) (@lem6932758 _127006 x s f)). Qed.
Lemma lem6932760 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term25 _127006 x s f) = (term148 _127006 x s f).
Proof. exact (TRANS (@lem6932718 _127006 f g x s h1) (@lem6932759 _127006 f g x s h1)). Qed.
Lemma lem6932761 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6932762 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term163 _127006 x s f) = (term164 _127006 x s f).
Proof. exact (MK_COMB (@lem6932761) (@lem6932760 _127006 f g x s h1)). Qed.
Lemma lem6932764 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term24 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6932217 _126525 x f s h0). Qed.
Lemma lem6932765 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) : term24 _127006 x s f.
Proof. exact (@lem6932764 _127006 x s f). Qed.
Lemma lem6932766 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : term24 _127006 x s g.
Proof. exact (@lem6932765 _127006 x s g). Qed.
Lemma lem6932768 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (@FINITE _127006 s) = True.
Proof. exact (EQ_MP (@lem6932518 _127006 s) (@lem6932517 _127006 f g x s h1)). Qed.
Lemma lem6932769 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : True = (@FINITE _127006 s).
Proof. exact (SYM (@lem6932768 _127006 f g x s h1)). Qed.
Lemma lem6932770 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : @FINITE _127006 s.
Proof. exact (EQ_MP (@lem6932769 _127006 f g x s h1) (@lem0)). Qed.
Lemma lem6932771 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term25 _127006 x s g) = (term26 _127006 x s g).
Proof. exact (@lem6932766 _127006 x s g (@lem6932770 _127006 f g x s h1)). Qed.
Lemma lem6932773 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term142 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6932774 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term143 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6932773 _2963 g t e g' t' e'). Qed.
Lemma lem6932775 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term144 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6932774 _2963 g t e g' t'). Qed.
Lemma lem6932776 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term145 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6932775 _2963 g t e g'). Qed.
Lemma lem6932777 (g : Prop) (t : nat) (e : nat) : term146 g t e.
Proof. exact (@lem6932776 nat g t e). Qed.
Lemma lem6932778 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : term147 _127006 x s g.
Proof. exact (@lem6932777 (@IN _127006 x s) (@nsum _127006 s g) (term148 _127006 x s g)). Qed.
Lemma lem6932779 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) : term149 _127006 x s g g'.
Proof. exact (@lem6932778 _127006 x s g g'). Qed.
Lemma lem6932780 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) : (term149 _127006 x s g g') = (term150 _127006 x s g g').
Proof. exact (eq_refl (term149 _127006 x s g g')). Qed.
Lemma lem6932781 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) : term150 _127006 x s g g'.
Proof. exact (EQ_MP (@lem6932780 _127006 x s g g') (@lem6932779 _127006 x s g g')). Qed.
Lemma lem6932782 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) (t' : nat) : term151 _127006 x s g g' t'.
Proof. exact (@lem6932781 _127006 x s g g' t'). Qed.
Lemma lem6932783 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) (t' : nat) : (term151 _127006 x s g g' t') = (term152 _127006 x s g g' t').
Proof. exact (eq_refl (term151 _127006 x s g g' t')). Qed.
Lemma lem6932784 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) (t' : nat) : term152 _127006 x s g g' t'.
Proof. exact (EQ_MP (@lem6932783 _127006 x s g g' t') (@lem6932782 _127006 x s g g' t')). Qed.
Lemma lem6932785 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) (t' : nat) (e' : nat) : term153 _127006 x s g g' t' e'.
Proof. exact (@lem6932784 _127006 x s g g' t' e'). Qed.
Lemma lem6932786 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term153 _127006 x s g g' t' e') = (term154 _127006 x s g g' t' e').
Proof. exact (eq_refl (term153 _127006 x s g g' t' e')). Qed.
Lemma lem6932787 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (g' : Prop) (t' : nat) (e' : nat) : term154 _127006 x s g g' t' e'.
Proof. exact (EQ_MP (@lem6932786 _127006 x s g g' t' e') (@lem6932785 _127006 x s g g' t' e')). Qed.
Lemma lem6932789 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (@IN _127006 x s) = False.
Proof. exact (@lem6932521 _127006 x s (@lem6932520 _127006 f g x s h1)). Qed.
Lemma lem6932790 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) (t' : nat) (e' : nat) : term155 _127006 x s g t' e'.
Proof. exact (@lem6932787 _127006 x s g False t' e'). Qed.
Lemma lem6932791 {_127006 : Type'} (t' : nat) (e' : nat) (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term156 _127006 x s g t' e'.
Proof. exact (@lem6932790 _127006 x s g t' e' (@lem6932789 _127006 f g x s h1)). Qed.
Lemma lem6932795 {_127006 : Type'} (s : _127006 -> Prop) (g : _127006 -> nat) : (@nsum _127006 s g) = (@nsum _127006 s g).
Proof. exact (eq_refl (@nsum _127006 s g)). Qed.
Lemma lem6932796 {_127006 : Type'} (s : _127006 -> Prop) (g : _127006 -> nat) : term157 _127006 s g.
Proof. exact (fun h0 : False => @lem6932795 _127006 s g). Qed.
Lemma lem6932797 {_127006 : Type'} (e' : nat) (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term158 _127006 x s g e'.
Proof. exact (@lem6932791 _127006 (@nsum _127006 s g) e' f g x s h1). Qed.
Lemma lem6932798 {_127006 : Type'} (e' : nat) (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term159 _127006 x s g e'.
Proof. exact (@lem6932797 _127006 e' f g x s h1 (@lem6932796 _127006 s g)). Qed.
Lemma lem6932804 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : (term148 _127006 x s g) = (term148 _127006 x s g).
Proof. exact (eq_refl (term148 _127006 x s g)). Qed.
Lemma lem6932805 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : term160 _127006 x s g.
Proof. exact (fun h0 : ~ False => @lem6932804 _127006 x s g). Qed.
Lemma lem6932806 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term161 _127006 x s g.
Proof. exact (@lem6932798 _127006 (term148 _127006 x s g) f g x s h1). Qed.
Lemma lem6932807 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term26 _127006 x s g) = (term162 _127006 x s g).
Proof. exact (@lem6932806 _127006 f g x s h1 (@lem6932805 _127006 x s g)). Qed.
Lemma lem6932809 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6932810 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6932809 nat t1 t2). Qed.
Lemma lem6932811 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : (term162 _127006 x s g) = (term148 _127006 x s g).
Proof. exact (@lem6932810 (@nsum _127006 s g) (term148 _127006 x s g)). Qed.
Lemma lem6932812 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term26 _127006 x s g) = (term148 _127006 x s g).
Proof. exact (TRANS (@lem6932807 _127006 f g x s h1) (@lem6932811 _127006 x s g)). Qed.
Lemma lem6932813 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term25 _127006 x s g) = (term148 _127006 x s g).
Proof. exact (TRANS (@lem6932771 _127006 f g x s h1) (@lem6932812 _127006 f g x s h1)). Qed.
Lemma lem6932814 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term119 _127006 f x s g) = (term165 _127006 f x s g).
Proof. exact (MK_COMB (@lem6932762 _127006 f g x s h1) (@lem6932813 _127006 f g x s h1)). Qed.
Lemma lem6932816 (m : nat) (n : nat) (p : nat) (q : nat) : term166 m n p q.
Proof. exact (fun h0 : term15 m p n q => @lem6932195 m p n q h0). Qed.
Lemma lem6932817 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : term167 _127006 f x s g.
Proof. exact (@lem6932816 (f x) (@nsum _127006 s f) (g x) (@nsum _127006 s g)). Qed.
Lemma lem6932821 {_127006 : Type'} (x' : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term168 _127006 x s f g x'.
Proof. exact (fun h0 : term6 _127006 x x' s => @lem6932703 _127006 f g x x' s h1 h0). Qed.
Lemma lem6932822 {_127006 : Type'} (x' : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term168 _127006 x s f g x'.
Proof. exact (@lem6932821 _127006 x' x s f g h1). Qed.
Lemma lem6932823 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term169 _127006 s f g x.
Proof. exact (@lem6932822 _127006 x x s f g h1). Qed.
Lemma lem6932827 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6932828 {_127006 : Type'} (x : _127006) : (x = x) = True.
Proof. exact (@lem6932827 _127006 x). Qed.
Lemma lem6932829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6932830 {_127006 : Type'} (x : _127006) : (term170 _127006 x) = (or True).
Proof. exact (MK_COMB (@lem6932829) (@lem6932828 _127006 x)). Qed.
Lemma lem6932832 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (@IN _127006 x s) = False.
Proof. exact (@lem6932521 _127006 x s (@lem6932520 _127006 f g x s h1)). Qed.
Lemma lem6932833 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term171 _127006 x s) = (True \/ False).
Proof. exact (MK_COMB (@lem6932830 _127006 x) (@lem6932832 _127006 f g x s h1)). Qed.
Lemma lem6932835 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem6932836 : (True \/ False) = True.
Proof. exact (@lem6932835 False). Qed.
Lemma lem6932837 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term171 _127006 x s) = True.
Proof. exact (TRANS (@lem6932833 _127006 f g x s h1) (@lem6932836)). Qed.
Lemma lem6932838 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : True = (term171 _127006 x s).
Proof. exact (SYM (@lem6932837 _127006 f g x s h1)). Qed.
Lemma lem6932839 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term171 _127006 x s.
Proof. exact (EQ_MP (@lem6932838 _127006 f g x s h1) (@lem0)). Qed.
Lemma lem6932840 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : (term125 _127006 f g x) = True.
Proof. exact (@lem6932823 _127006 x s f g h1 (@lem6932839 _127006 f g x s h2)). Qed.
Lemma lem6932841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6932842 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : (term172 _127006 f g x) = (and True).
Proof. exact (MK_COMB (@lem6932841) (@lem6932840 _127006 f g x s h1 h2)). Qed.
Lemma lem6932844 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term173 _127006 f s g.
Proof. exact (fun h0 : term40 _127006 s f g => @lem6932527 _127006 f g x s h0 h1). Qed.
Lemma lem6932903 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6932904 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem6932903 p q p' q'). Qed.
Lemma lem6932905 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem6932904 p q p'). Qed.
Lemma lem6932906 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) : term174 _127006 s f g _92418.
Proof. exact (@lem6932905 (@IN _127006 _92418 s) (term125 _127006 f g _92418)). Qed.
Lemma lem6932907 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (p' : Prop) : term175 _127006 s f g _92418 p'.
Proof. exact (@lem6932906 _127006 s f g _92418 p'). Qed.
Lemma lem6932908 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (p' : Prop) : (term175 _127006 s f g _92418 p') = (term176 _127006 s f g _92418 p').
Proof. exact (eq_refl (term175 _127006 s f g _92418 p')). Qed.
Lemma lem6932909 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (p' : Prop) : term176 _127006 s f g _92418 p'.
Proof. exact (EQ_MP (@lem6932908 _127006 s f g _92418 p') (@lem6932907 _127006 s f g _92418 p')). Qed.
Lemma lem6932910 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (p' : Prop) (q' : Prop) : term177 _127006 s f g _92418 p' q'.
Proof. exact (@lem6932909 _127006 s f g _92418 p' q'). Qed.
Lemma lem6932911 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (p' : Prop) (q' : Prop) : (term177 _127006 s f g _92418 p' q') = (term178 _127006 s f g _92418 p' q').
Proof. exact (eq_refl (term177 _127006 s f g _92418 p' q')). Qed.
Lemma lem6932912 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (p' : Prop) (q' : Prop) : term178 _127006 s f g _92418 p' q'.
Proof. exact (EQ_MP (@lem6932911 _127006 s f g _92418 p' q') (@lem6932910 _127006 s f g _92418 p' q')). Qed.
Lemma lem6932913 {_127006 : Type'} (_92418 : _127006) (s : _127006 -> Prop) : (@IN _127006 _92418 s) = (@IN _127006 _92418 s).
Proof. exact (eq_refl (@IN _127006 _92418 s)). Qed.
Lemma lem6932914 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (s : _127006 -> Prop) (q' : Prop) : term179 _127006 f g _92418 s q'.
Proof. exact (@lem6932912 _127006 s f g _92418 (@IN _127006 _92418 s) q'). Qed.
Lemma lem6932915 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (s : _127006 -> Prop) (q' : Prop) : term180 _127006 f g _92418 s q'.
Proof. exact (@lem6932914 _127006 f g _92418 s q' (@lem6932913 _127006 _92418 s)). Qed.
Lemma lem6932916 {_127006 : Type'} (_92418 : _127006) (s : _127006 -> Prop) (h1 : @IN _127006 _92418 s) : @IN _127006 _92418 s.
Proof. exact (h1). Qed.
Lemma lem6932917 {_127006 : Type'} (_92418 : _127006) (s : _127006 -> Prop) : (@IN _127006 _92418 s) = ((@IN _127006 _92418 s) = True).
Proof. exact (@lem7 (@IN _127006 _92418 s)). Qed.
Lemma lem6932920 {_127006 : Type'} (x' : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term168 _127006 x s f g x'.
Proof. exact (fun h0 : term6 _127006 x x' s => @lem6932703 _127006 f g x x' s h1 h0). Qed.
Lemma lem6932921 {_127006 : Type'} (x' : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term168 _127006 x s f g x'.
Proof. exact (@lem6932920 _127006 x' x s f g h1). Qed.
Lemma lem6932922 {_127006 : Type'} (_92418 : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term168 _127006 x s f g _92418.
Proof. exact (@lem6932921 _127006 _92418 x s f g h1). Qed.
Lemma lem6932928 {_127006 : Type'} (_92418 : _127006) (s : _127006 -> Prop) (h1 : @IN _127006 _92418 s) : (@IN _127006 _92418 s) = True.
Proof. exact (EQ_MP (@lem6932917 _127006 _92418 s) (@lem6932916 _127006 _92418 s h1)). Qed.
Lemma lem6932929 {_127006 : Type'} (_92418 : _127006) (x : _127006) : (term181 _127006 _92418 x) = (term181 _127006 _92418 x).
Proof. exact (eq_refl (term181 _127006 _92418 x)). Qed.
Lemma lem6932930 {_127006 : Type'} (x : _127006) (_92418 : _127006) (s : _127006 -> Prop) (h1 : @IN _127006 _92418 s) : (term6 _127006 x _92418 s) = (term182 _127006 _92418 x).
Proof. exact (MK_COMB (@lem6932929 _127006 _92418 x) (@lem6932928 _127006 _92418 s h1)). Qed.
Lemma lem6932932 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem6932933 {_127006 : Type'} (_92418 : _127006) (x : _127006) : (term182 _127006 _92418 x) = True.
Proof. exact (@lem6932932 (_92418 = x)). Qed.
Lemma lem6932934 {_127006 : Type'} (x : _127006) (_92418 : _127006) (s : _127006 -> Prop) (h1 : @IN _127006 _92418 s) : (term6 _127006 x _92418 s) = True.
Proof. exact (TRANS (@lem6932930 _127006 x _92418 s h1) (@lem6932933 _127006 _92418 x)). Qed.
Lemma lem6932935 {_127006 : Type'} (x : _127006) (_92418 : _127006) (s : _127006 -> Prop) (h1 : @IN _127006 _92418 s) : True = (term6 _127006 x _92418 s).
Proof. exact (SYM (@lem6932934 _127006 x _92418 s h1)). Qed.
Lemma lem6932936 {_127006 : Type'} (x : _127006) (_92418 : _127006) (s : _127006 -> Prop) (h1 : @IN _127006 _92418 s) : term6 _127006 x _92418 s.
Proof. exact (EQ_MP (@lem6932935 _127006 x _92418 s h1) (@lem0)). Qed.
Lemma lem6932937 {_127006 : Type'} (x : _127006) (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : @IN _127006 _92418 s) : (term125 _127006 f g _92418) = True.
Proof. exact (@lem6932922 _127006 _92418 x s f g h1 (@lem6932936 _127006 x _92418 s h2)). Qed.
Lemma lem6932938 {_127006 : Type'} (_92418 : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term183 _127006 s f g _92418.
Proof. exact (fun h0 : @IN _127006 _92418 s => @lem6932937 _127006 x f g _92418 s h1 h0). Qed.
Lemma lem6932939 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (_92418 : _127006) (s : _127006 -> Prop) : term184 _127006 f g _92418 s.
Proof. exact (@lem6932915 _127006 f g _92418 s True). Qed.
Lemma lem6932940 {_127006 : Type'} (_92418 : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : (term185 _127006 s f g _92418) = (term186 _127006 _92418 s).
Proof. exact (@lem6932939 _127006 f g _92418 s (@lem6932938 _127006 _92418 x s f g h1)). Qed.
Lemma lem6932942 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6932943 {_127006 : Type'} (_92418 : _127006) (s : _127006 -> Prop) : (term186 _127006 _92418 s) = True.
Proof. exact (@lem6932942 (@IN _127006 _92418 s)). Qed.
Lemma lem6932944 {_127006 : Type'} (_92418 : _127006) (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : (term185 _127006 s f g _92418) = True.
Proof. exact (TRANS (@lem6932940 _127006 _92418 x s f g h1) (@lem6932943 _127006 _92418 s)). Qed.
Lemma lem6932947 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : (term187 _127006 s f g) = (term188 _127006).
Proof. exact (fun_ext (fun _92418 : _127006 => @lem6932944 _127006 _92418 x s f g h1)). Qed.
Lemma lem6932948 {_127006 : Type'} : (@all _127006) = (@all _127006).
Proof. exact (eq_refl (@all _127006)). Qed.
Lemma lem6932949 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : (term40 _127006 s f g) = (term189 _127006).
Proof. exact (MK_COMB (@lem6932948 _127006) (@lem6932947 _127006 x s f g h1)). Qed.
Lemma lem6932951 {A : Type'} (t : Prop) : (term190 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6932952 {_127006 : Type'} (t : Prop) : (term190 _127006 t) = t.
Proof. exact (@lem6932951 _127006 t). Qed.
Lemma lem6932953 {_127006 : Type'} : (term189 _127006) = True.
Proof. exact (@lem6932952 _127006 True). Qed.
Lemma lem6932954 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : (term40 _127006 s f g) = True.
Proof. exact (TRANS (@lem6932949 _127006 x s f g h1) (@lem6932953 _127006)). Qed.
Lemma lem6932955 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : True = (term40 _127006 s f g).
Proof. exact (SYM (@lem6932954 _127006 x s f g h1)). Qed.
Lemma lem6932956 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term138 _127006 x s f g) : term40 _127006 s f g.
Proof. exact (EQ_MP (@lem6932955 _127006 x s f g h1) (@lem0)). Qed.
Lemma lem6932957 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : (term41 _127006 f s g) = True.
Proof. exact (@lem6932844 _127006 f g x s h2 (@lem6932956 _127006 x s f g h1)). Qed.
Lemma lem6932958 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : (term191 _127006 x f s g) = (True /\ True).
Proof. exact (MK_COMB (@lem6932842 _127006 f g x s h1 h2) (@lem6932957 _127006 f g x s h1 h2)). Qed.
Lemma lem6932960 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6932961 : (True /\ True) = True.
Proof. exact (@lem6932960 True). Qed.
Lemma lem6932962 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : (term191 _127006 x f s g) = True.
Proof. exact (TRANS (@lem6932958 _127006 f g x s h1 h2) (@lem6932961)). Qed.
Lemma lem6932963 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : True = (term191 _127006 x f s g).
Proof. exact (SYM (@lem6932962 _127006 f g x s h1 h2)). Qed.
Lemma lem6932964 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : term191 _127006 x f s g.
Proof. exact (EQ_MP (@lem6932963 _127006 f g x s h1 h2) (@lem0)). Qed.
Lemma lem6932965 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : (term165 _127006 f x s g) = True.
Proof. exact (@lem6932817 _127006 f x s g (@lem6932964 _127006 f g x s h1 h2)). Qed.
Lemma lem6932966 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term138 _127006 x s f g) (h2 : term66 _127006 f g x s) : (term119 _127006 f x s g) = True.
Proof. exact (TRANS (@lem6932814 _127006 f g x s h2) (@lem6932965 _127006 f g x s h1 h2)). Qed.
Lemma lem6932967 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : term192 _127006 f x s g.
Proof. exact (fun h0 : term138 _127006 x s f g => @lem6932966 _127006 f g x s h0 h1). Qed.
Lemma lem6932968 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) : term193 _127006 x s f g.
Proof. exact (@lem6932695 _127006 x s f g True). Qed.
Lemma lem6932969 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term70 _127006 f x s g) = (term194 _127006 x s f g).
Proof. exact (@lem6932968 _127006 x s f g (@lem6932967 _127006 f g x s h1)). Qed.
Lemma lem6932971 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6932972 {_127006 : Type'} (x : _127006) (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) : (term194 _127006 x s f g) = True.
Proof. exact (@lem6932971 (term138 _127006 x s f g)). Qed.
Lemma lem6932973 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (h1 : term66 _127006 f g x s) : (term70 _127006 f x s g) = True.
Proof. exact (TRANS (@lem6932969 _127006 f g x s h1) (@lem6932972 _127006 x s f g)). Qed.
Lemma lem6932974 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : term195 _127006 f x s g.
Proof. exact (fun h0 : term66 _127006 f g x s => @lem6932973 _127006 f g x s h0). Qed.
Lemma lem6932975 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) : term196 _127006 f g x s.
Proof. exact (@lem6932514 _127006 f g x s True). Qed.
Lemma lem6932976 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) : (term72 _127006 f x s g) = (term197 _127006 f g x s).
Proof. exact (@lem6932975 _127006 f g x s (@lem6932974 _127006 f x s g)). Qed.
Lemma lem6932978 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6932979 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) : (term197 _127006 f g x s) = True.
Proof. exact (@lem6932978 (term66 _127006 f g x s)). Qed.
Lemma lem6932980 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (s : _127006 -> Prop) (g : _127006 -> nat) : (term72 _127006 f x s g) = True.
Proof. exact (TRANS (@lem6932976 _127006 f g x s) (@lem6932979 _127006 f g x s)). Qed.
Lemma lem6932981 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (g : _127006 -> nat) : (term74 _127006 f x g) = (term198 _127006).
Proof. exact (fun_ext (fun s : _127006 -> Prop => @lem6932980 _127006 f x s g)). Qed.
Lemma lem6932982 {_127006 : Type'} : (@all (_127006 -> Prop)) = (@all (_127006 -> Prop)).
Proof. exact (eq_refl (@all (_127006 -> Prop))). Qed.
Lemma lem6932983 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (g : _127006 -> nat) : (term76 _127006 f x g) = (term199 _127006).
Proof. exact (MK_COMB (@lem6932982 _127006) (@lem6932981 _127006 f x g)). Qed.
Lemma lem6932985 {A : Type'} (t : Prop) : (term190 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6932986 {_127006 : Type'} (t : Prop) : (term200 _127006 t) = t.
Proof. exact (@lem6932985 (_127006 -> Prop) t). Qed.
Lemma lem6932987 {_127006 : Type'} : (term199 _127006) = True.
Proof. exact (@lem6932986 _127006 True). Qed.
Lemma lem6932988 {_127006 : Type'} (f : _127006 -> nat) (x : _127006) (g : _127006 -> nat) : (term76 _127006 f x g) = True.
Proof. exact (TRANS (@lem6932983 _127006 f x g) (@lem6932987 _127006)). Qed.
Lemma lem6932989 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term78 _127006 f g) = (term188 _127006).
Proof. exact (fun_ext (fun x : _127006 => @lem6932988 _127006 f x g)). Qed.
Lemma lem6932990 {_127006 : Type'} : (@all _127006) = (@all _127006).
Proof. exact (eq_refl (@all _127006)). Qed.
Lemma lem6932991 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term80 _127006 f g) = (term189 _127006).
Proof. exact (MK_COMB (@lem6932990 _127006) (@lem6932989 _127006 f g)). Qed.
Lemma lem6932993 {A : Type'} (t : Prop) : (term190 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6932994 {_127006 : Type'} (t : Prop) : (term190 _127006 t) = t.
Proof. exact (@lem6932993 _127006 t). Qed.
Lemma lem6932995 {_127006 : Type'} : (term189 _127006) = True.
Proof. exact (@lem6932994 _127006 True). Qed.
Lemma lem6932996 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term80 _127006 f g) = True.
Proof. exact (TRANS (@lem6932991 _127006 f g) (@lem6932995 _127006)). Qed.
Lemma lem6932997 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term82 _127006 f g) = (True /\ True).
Proof. exact (MK_COMB (@lem6932387 _127006 f g) (@lem6932996 _127006 f g)). Qed.
Lemma lem6932999 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6933000 : (True /\ True) = True.
Proof. exact (@lem6932999 True). Qed.
Lemma lem6933001 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term82 _127006 f g) = True.
Proof. exact (TRANS (@lem6932997 _127006 f g) (@lem6933000)). Qed.
Lemma lem6933002 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : True = (term82 _127006 f g).
Proof. exact (SYM (@lem6933001 _127006 f g)). Qed.
Lemma lem6933003 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term82 _127006 f g.
Proof. exact (EQ_MP (@lem6933002 _127006 f g) (@lem0)). Qed.
Lemma lem6933004 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term45 _127006 f g.
Proof. exact (@lem6932300 _127006 f g (@lem6933003 _127006 f g)). Qed.
Lemma lem6933009 {_127006 : Type'} (f : _127006 -> nat) : term49 _127006 f.
Proof. exact (fun g : _127006 -> nat => @lem6933004 _127006 f g). Qed.
Lemma lem6933014 {_127006 : Type'} : term53 _127006.
Proof. exact (fun f : _127006 -> nat => @lem6933009 _127006 f). Qed.
Lemma lem6933015 {_127006 : Type'} : term52 _127006.
Proof. exact (EQ_MP (@lem6932267 _127006) (@lem6933014 _127006)). Qed.
