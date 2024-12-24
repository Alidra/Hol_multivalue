Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CARD_LE_IMAGE_term_abbrevs.
Require Import CARD_IMAGE_LE_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import LE_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4008004 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4008005 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4008006 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4008005 t1) (@lem4008004 t1)). Qed.
Lemma lem4008007 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4008006 t1 t2). Qed.
Lemma lem4008008 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4008009 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4008008 t1 t2) (@lem4008007 t1 t2)). Qed.
Lemma lem4008010 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4008009 t1 t2 t3). Qed.
Lemma lem4008011 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4008012 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4008011 t1 t2 t3) (@lem4008010 t1 t2 t3)). Qed.
Lemma lem4008013 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4008012 t1 t2 t3)). Qed.
Lemma lem4008015 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4008016 {A B : Type'} : (term8 A B) = (term9 A B).
Proof. exact (@lem4008015 (term8 A B)). Qed.
Lemma lem4008017 {A B : Type'} : (term9 A B) = (term8 A B).
Proof. exact (SYM (@lem4008016 A B)). Qed.
Lemma lem4008018 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem4008019 {A B : Type'} : term11 A B.
Proof. exact (@lem4008003 A B). Qed.
Lemma lem4008020 {B : Type'} : term12 B.
Proof. exact (@lem4008003 B B). Qed.
Lemma lem4008021 {A : Type'} : term12 A.
Proof. exact (@lem4008003 A A). Qed.
Lemma lem4008026 {A B : Type'} : term13 A B.
Proof. exact (@lem3615104 A B). Qed.
Lemma lem4008027 {B : Type'} : term14 B.
Proof. exact (@lem3615104 B B). Qed.
Lemma lem4008028 {A : Type'} : term14 A.
Proof. exact (@lem3615104 A A). Qed.
Lemma lem4008035 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem4008036 {A B : Type'} : term16 A B.
Proof. exact (fun h0 : term15 A B => @lem4008035 A B h0). Qed.
Lemma lem4008037 {A B : Type'} (h1 : term16 A B) : term16 A B.
Proof. exact (h1). Qed.
Lemma lem4008038 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem4008039 {A B : Type'} (h1 : term15 A B) (h2 : term16 A B) : term15 A B.
Proof. exact (@lem4008037 A B h2 (@lem4008038 A B h1)). Qed.
Lemma lem4008040 {A B : Type'} (h1 : term15 A B) : term17 A B.
Proof. exact (fun h0 : term16 A B => @lem4008039 A B h1 h0). Qed.
Lemma lem4008041 {A B : Type'} (h1 : term16 A B) : term16 A B.
Proof. exact (h1). Qed.
Lemma lem4008042 {A B : Type'} (h1 : term15 A B) (h2 : term16 A B) : term15 A B.
Proof. exact (@lem4008040 A B h1 (@lem4008041 A B h2)). Qed.
Lemma lem4008043 {A B : Type'} (h1 : term16 A B) : term16 A B.
Proof. exact (fun h0 : term15 A B => @lem4008042 A B h0 h1). Qed.
Lemma lem4008044 {A B : Type'} : term18 A B.
Proof. exact (fun h0 : term16 A B => @lem4008043 A B h0). Qed.
Lemma lem4008047 {A B : Type'} : term16 A B.
Proof. exact (@lem4008044 A B (@lem4008036 A B)). Qed.
Lemma lem4008048 {A B : Type'} : term16 A B.
Proof. exact (@lem4008047 A B). Qed.
Lemma lem4008148 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4008149 {B : Type'} : (term19 B) = (term20 B).
Proof. exact (@lem4008148 (term12 B)). Qed.
Lemma lem4008160 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (eq_refl (term21 A B)). Qed.
Lemma lem4008161 {A B : Type'} : (term22 A B) = (term23 A B).
Proof. exact (MK_COMB (@lem4008160 A B) (@lem4008149 B)). Qed.
Lemma lem4008164 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (eq_refl (term24 A)). Qed.
Lemma lem4008165 {A B : Type'} : (term25 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem4008164 A) (@lem4008161 A B)). Qed.
Lemma lem4008168 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem4008169 {A B : Type'} : (term28 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem4008168) (@lem4008165 A B)). Qed.
Lemma lem4008172 {B : Type'} : (term30 B) = (term30 B).
Proof. exact (eq_refl (term30 B)). Qed.
Lemma lem4008173 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4008172 B) (@lem4008169 A B)). Qed.
Lemma lem4008176 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (eq_refl (term33 A B)). Qed.
Lemma lem4008177 {A B : Type'} : (term34 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem4008176 A B) (@lem4008173 A B)). Qed.
Lemma lem4008180 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (eq_refl (term30 A)). Qed.
Lemma lem4008181 {A B : Type'} : (term36 A B) = (term37 A B).
Proof. exact (MK_COMB (@lem4008180 A) (@lem4008177 A B)). Qed.
Lemma lem4008184 {A B : Type'} : (term38 A B) = (term38 A B).
Proof. exact (eq_refl (term38 A B)). Qed.
Lemma lem4008191 {A B : Type'} : (term15 A B) = (term39 A B).
Proof. exact (MK_COMB (@lem4008184 A B) (@lem4008181 A B)). Qed.
Lemma lem4008196 {B : Type'} (f : B -> B) (s : B -> Prop) : (term40 B f s) = (term40 B f s).
Proof. exact (eq_refl (term40 B f s)). Qed.
Lemma lem4008197 {B : Type'} (f : B -> B) : (term41 B f) = (term41 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4008196 B f s)). Qed.
Lemma lem4008198 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4008199 {B : Type'} (f : B -> B) : (term42 B f) = (term42 B f).
Proof. exact (MK_COMB (@lem4008198 B) (@lem4008197 B f)). Qed.
Lemma lem4008200 {B : Type'} : (term43 B) = (term43 B).
Proof. exact (fun_ext (fun f : B -> B => @lem4008199 B f)). Qed.
Lemma lem4008201 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4008202 {B : Type'} : (term12 B) = (term12 B).
Proof. exact (MK_COMB (@lem4008201 B) (@lem4008200 B)). Qed.
Lemma lem4008203 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4008204 {B : Type'} : (term20 B) = (term20 B).
Proof. exact (MK_COMB (@lem4008203) (@lem4008202 B)). Qed.
Lemma lem4008209 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term44 A B f s) = (term44 A B f s).
Proof. exact (eq_refl (term44 A B f s)). Qed.
Lemma lem4008210 {A B : Type'} (f : A -> B) : (term45 A B f) = (term45 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4008209 A B f s)). Qed.
Lemma lem4008211 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4008212 {A B : Type'} (f : A -> B) : (term46 A B f) = (term46 A B f).
Proof. exact (MK_COMB (@lem4008211 A) (@lem4008210 A B f)). Qed.
Lemma lem4008213 {A B : Type'} : (term47 A B) = (term47 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4008212 A B f)). Qed.
Lemma lem4008214 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4008215 {A B : Type'} : (term11 A B) = (term11 A B).
Proof. exact (MK_COMB (@lem4008214 A B) (@lem4008213 A B)). Qed.
Lemma lem4008216 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4008217 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (MK_COMB (@lem4008216) (@lem4008215 A B)). Qed.
Lemma lem4008218 {A B : Type'} : (term23 A B) = (term23 A B).
Proof. exact (MK_COMB (@lem4008217 A B) (@lem4008204 B)). Qed.
Lemma lem4008223 {A : Type'} (f : A -> A) (s : A -> Prop) : (term40 A f s) = (term40 A f s).
Proof. exact (eq_refl (term40 A f s)). Qed.
Lemma lem4008224 {A : Type'} (f : A -> A) : (term41 A f) = (term41 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4008223 A f s)). Qed.
Lemma lem4008225 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4008226 {A : Type'} (f : A -> A) : (term42 A f) = (term42 A f).
Proof. exact (MK_COMB (@lem4008225 A) (@lem4008224 A f)). Qed.
Lemma lem4008227 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4008226 A f)). Qed.
Lemma lem4008228 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4008229 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem4008228 A) (@lem4008227 A)). Qed.
Lemma lem4008230 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4008231 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem4008230) (@lem4008229 A)). Qed.
Lemma lem4008232 {A B : Type'} : (term26 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem4008231 A) (@lem4008218 A B)). Qed.
Lemma lem4008241 (n : nat) (m : nat) (p : nat) : (term48 n m p) = (term48 n m p).
Proof. exact (eq_refl (term48 n m p)). Qed.
Lemma lem4008242 (n : nat) (m : nat) : (term49 n m) = (term49 n m).
Proof. exact (fun_ext (fun p : nat => @lem4008241 n m p)). Qed.
Lemma lem4008243 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4008244 (n : nat) (m : nat) : (term50 n m) = (term50 n m).
Proof. exact (MK_COMB (@lem4008243) (@lem4008242 n m)). Qed.
Lemma lem4008245 (m : nat) : (term51 m) = (term51 m).
Proof. exact (fun_ext (fun n : nat => @lem4008244 n m)). Qed.
Lemma lem4008246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4008247 (m : nat) : (term52 m) = (term52 m).
Proof. exact (MK_COMB (@lem4008246) (@lem4008245 m)). Qed.
Lemma lem4008248 : term53 = term53.
Proof. exact (fun_ext (fun m : nat => @lem4008247 m)). Qed.
Lemma lem4008249 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4008250 : term54 = term54.
Proof. exact (MK_COMB (@lem4008249) (@lem4008248)). Qed.
Lemma lem4008251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4008252 : term27 = term27.
Proof. exact (MK_COMB (@lem4008251) (@lem4008250)). Qed.
Lemma lem4008253 {A B : Type'} : (term29 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem4008252) (@lem4008232 A B)). Qed.
Lemma lem4008258 {B : Type'} (f : B -> B) (s : B -> Prop) : (term55 B f s) = (term55 B f s).
Proof. exact (eq_refl (term55 B f s)). Qed.
Lemma lem4008259 {B : Type'} (f : B -> B) : (term56 B f) = (term56 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4008258 B f s)). Qed.
Lemma lem4008260 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4008261 {B : Type'} (f : B -> B) : (term57 B f) = (term57 B f).
Proof. exact (MK_COMB (@lem4008260 B) (@lem4008259 B f)). Qed.
Lemma lem4008262 {B : Type'} : (term58 B) = (term58 B).
Proof. exact (fun_ext (fun f : B -> B => @lem4008261 B f)). Qed.
Lemma lem4008263 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4008264 {B : Type'} : (term14 B) = (term14 B).
Proof. exact (MK_COMB (@lem4008263 B) (@lem4008262 B)). Qed.
Lemma lem4008265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4008266 {B : Type'} : (term30 B) = (term30 B).
Proof. exact (MK_COMB (@lem4008265) (@lem4008264 B)). Qed.
Lemma lem4008267 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4008266 B) (@lem4008253 A B)). Qed.
Lemma lem4008272 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term59 A B f s) = (term59 A B f s).
Proof. exact (eq_refl (term59 A B f s)). Qed.
Lemma lem4008273 {A B : Type'} (f : A -> B) : (term60 A B f) = (term60 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4008272 A B f s)). Qed.
Lemma lem4008274 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4008275 {A B : Type'} (f : A -> B) : (term61 A B f) = (term61 A B f).
Proof. exact (MK_COMB (@lem4008274 A) (@lem4008273 A B f)). Qed.
Lemma lem4008276 {A B : Type'} : (term62 A B) = (term62 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4008275 A B f)). Qed.
Lemma lem4008277 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4008278 {A B : Type'} : (term13 A B) = (term13 A B).
Proof. exact (MK_COMB (@lem4008277 A B) (@lem4008276 A B)). Qed.
Lemma lem4008279 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4008280 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (MK_COMB (@lem4008279) (@lem4008278 A B)). Qed.
Lemma lem4008281 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem4008280 A B) (@lem4008267 A B)). Qed.
Lemma lem4008286 {A : Type'} (f : A -> A) (s : A -> Prop) : (term55 A f s) = (term55 A f s).
Proof. exact (eq_refl (term55 A f s)). Qed.
Lemma lem4008287 {A : Type'} (f : A -> A) : (term56 A f) = (term56 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4008286 A f s)). Qed.
Lemma lem4008288 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4008289 {A : Type'} (f : A -> A) : (term57 A f) = (term57 A f).
Proof. exact (MK_COMB (@lem4008288 A) (@lem4008287 A f)). Qed.
Lemma lem4008290 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4008289 A f)). Qed.
Lemma lem4008291 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4008292 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (MK_COMB (@lem4008291 A) (@lem4008290 A)). Qed.
Lemma lem4008293 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4008294 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem4008293) (@lem4008292 A)). Qed.
Lemma lem4008295 {A B : Type'} : (term37 A B) = (term37 A B).
Proof. exact (MK_COMB (@lem4008294 A) (@lem4008281 A B)). Qed.
Lemma lem4008308 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term63 A B f s n) = (term63 A B f s n).
Proof. exact (eq_refl (term63 A B f s n)). Qed.
Lemma lem4008309 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term64 A B f s) = (term64 A B f s).
Proof. exact (fun_ext (fun n : nat => @lem4008308 A B f s n)). Qed.
Lemma lem4008310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4008311 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term65 A B f s) = (term65 A B f s).
Proof. exact (MK_COMB (@lem4008310) (@lem4008309 A B f s)). Qed.
Lemma lem4008312 {A B : Type'} (f : A -> B) : (term66 A B f) = (term66 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4008311 A B f s)). Qed.
Lemma lem4008313 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4008314 {A B : Type'} (f : A -> B) : (term67 A B f) = (term67 A B f).
Proof. exact (MK_COMB (@lem4008313 A) (@lem4008312 A B f)). Qed.
Lemma lem4008315 {A B : Type'} : (term68 A B) = (term68 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4008314 A B f)). Qed.
Lemma lem4008316 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4008317 {A B : Type'} : (term8 A B) = (term8 A B).
Proof. exact (MK_COMB (@lem4008316 A B) (@lem4008315 A B)). Qed.
Lemma lem4008318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4008319 {A B : Type'} : (term10 A B) = (term10 A B).
Proof. exact (MK_COMB (@lem4008318) (@lem4008317 A B)). Qed.
Lemma lem4008320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4008321 {A B : Type'} : (term38 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem4008320) (@lem4008319 A B)). Qed.
Lemma lem4008322 {A B : Type'} : (term39 A B) = (term39 A B).
Proof. exact (MK_COMB (@lem4008321 A B) (@lem4008295 A B)). Qed.
Lemma lem4008469 {A B : Type'} : (term15 A B) = (term39 A B).
Proof. exact (TRANS (@lem4008191 A B) (@lem4008322 A B)). Qed.
Lemma lem4008470 {A B : Type'} : (term39 A B) = (term15 A B).
Proof. exact (SYM (@lem4008469 A B)). Qed.
Lemma lem4008471 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem4008473 {A B : Type'} (h1 : term13 A B) : term13 A B.
Proof. exact (h1). Qed.
Lemma lem4008475 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem4008477 {A B : Type'} (h1 : term11 A B) : term11 A B.
Proof. exact (h1). Qed.
Lemma lem4008490 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term69 A B f s n) = (term70 A B f s n).
Proof. exact (@lem17045 (term71 A B f s) (term72 A B f s n)). Qed.
Lemma lem4008492 {A : Type'} (s : A -> Prop) (n : nat) : (term73 A s n) = (term73 A s n).
Proof. exact (eq_refl (term73 A s n)). Qed.
Lemma lem4008493 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term74 A B f s n) = (term75 A B f s n).
Proof. exact (MK_COMB (@lem4008492 A s n) (@lem4008490 A B f s n)). Qed.
Lemma lem4008494 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term76 A B f s n) = (term74 A B f s n).
Proof. exact (@lem17362 (term77 A s n) (term78 A B f s n)). Qed.
Lemma lem4008495 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term76 A B f s n) = (term75 A B f s n).
Proof. exact (TRANS (@lem4008494 A B f s n) (@lem4008493 A B f s n)). Qed.
Lemma lem4008496 (P : nat -> Prop) : (term79 P) = (term80 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4008497 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term81 A B f s) = (term82 A B f s).
Proof. exact (@lem4008496 (term64 A B f s)). Qed.
Lemma lem4008498 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term83 A B f s n) = (term63 A B f s n).
Proof. exact (eq_refl (term83 A B f s n)). Qed.
Lemma lem4008499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4008500 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term84 A B f s n) = (term76 A B f s n).
Proof. exact (MK_COMB (@lem4008499) (@lem4008498 A B f s n)). Qed.
Lemma lem4008501 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term84 A B f s n) = (term75 A B f s n).
Proof. exact (TRANS (@lem4008500 A B f s n) (@lem4008495 A B f s n)). Qed.
Lemma lem4008502 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term85 A B f s) = (term86 A B f s).
Proof. exact (fun_ext (fun n : nat => @lem4008501 A B f s n)). Qed.
Lemma lem4008503 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4008504 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term82 A B f s) = (term87 A B f s).
Proof. exact (MK_COMB (@lem4008503) (@lem4008502 A B f s)). Qed.
Lemma lem4008505 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term81 A B f s) = (term87 A B f s).
Proof. exact (TRANS (@lem4008497 A B f s) (@lem4008504 A B f s)). Qed.
Lemma lem4008506 {A : Type'} (P : type686 A) : (term88 A P) = (term89 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4008507 {A B : Type'} (f : A -> B) : (term90 A B f) = (term91 A B f).
Proof. exact (@lem4008506 A (term66 A B f)). Qed.
Lemma lem4008508 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term92 A B f s) = (term65 A B f s).
Proof. exact (eq_refl (term92 A B f s)). Qed.
Lemma lem4008509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4008510 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term93 A B f s) = (term81 A B f s).
Proof. exact (MK_COMB (@lem4008509) (@lem4008508 A B f s)). Qed.
Lemma lem4008511 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term93 A B f s) = (term87 A B f s).
Proof. exact (TRANS (@lem4008510 A B f s) (@lem4008505 A B f s)). Qed.
Lemma lem4008512 {A B : Type'} (f : A -> B) : (term94 A B f) = (term95 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4008511 A B f s)). Qed.
Lemma lem4008513 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4008514 {A B : Type'} (f : A -> B) : (term91 A B f) = (term96 A B f).
Proof. exact (MK_COMB (@lem4008513 A) (@lem4008512 A B f)). Qed.
Lemma lem4008515 {A B : Type'} (f : A -> B) : (term90 A B f) = (term96 A B f).
Proof. exact (TRANS (@lem4008507 A B f) (@lem4008514 A B f)). Qed.
Lemma lem4008516 {A B : Type'} (P : type572 A B) : (term97 A B P) = (term98 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem4008517 {A B : Type'} : (term10 A B) = (term99 A B).
Proof. exact (@lem4008516 A B (term68 A B)). Qed.
Lemma lem4008518 {A B : Type'} (f : A -> B) : (term100 A B f) = (term67 A B f).
Proof. exact (eq_refl (term100 A B f)). Qed.
Lemma lem4008519 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4008520 {A B : Type'} (f : A -> B) : (term101 A B f) = (term90 A B f).
Proof. exact (MK_COMB (@lem4008519) (@lem4008518 A B f)). Qed.
Lemma lem4008521 {A B : Type'} (f : A -> B) : (term101 A B f) = (term96 A B f).
Proof. exact (TRANS (@lem4008520 A B f) (@lem4008515 A B f)). Qed.
Lemma lem4008522 {A B : Type'} : (term102 A B) = (term103 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4008521 A B f)). Qed.
Lemma lem4008523 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4008524 {A B : Type'} : (term99 A B) = (term104 A B).
Proof. exact (MK_COMB (@lem4008523 A B) (@lem4008522 A B)). Qed.
Lemma lem4008585 {A B : Type'} : (term10 A B) = (term104 A B).
Proof. exact (TRANS (@lem4008517 A B) (@lem4008524 A B)). Qed.
Lemma lem4008586 {A B : Type'} (h1 : term10 A B) : term104 A B.
Proof. exact (EQ_MP (@lem4008585 A B) (@lem4008471 A B h1)). Qed.
Lemma lem4008663 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term59 A B f s) = (term105 A B f s).
Proof. exact (@lem17265 (@FINITE A s) (term71 A B f s)). Qed.
Lemma lem4008664 {A B : Type'} (f : A -> B) : (term60 A B f) = (term106 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4008663 A B f s)). Qed.
Lemma lem4008665 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4008666 {A B : Type'} (f : A -> B) : (term61 A B f) = (term107 A B f).
Proof. exact (MK_COMB (@lem4008665 A) (@lem4008664 A B f)). Qed.
Lemma lem4008667 {A B : Type'} : (term62 A B) = (term108 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4008666 A B f)). Qed.
Lemma lem4008668 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4008725 {A B : Type'} : (term13 A B) = (term109 A B).
Proof. exact (MK_COMB (@lem4008668 A B) (@lem4008667 A B)). Qed.
Lemma lem4008726 {A B : Type'} (h1 : term13 A B) : term109 A B.
Proof. exact (EQ_MP (@lem4008725 A B) (@lem4008473 A B h1)). Qed.
Lemma lem4008803 (m : nat) (n : nat) (p : nat) : (term110 m n p) = (term111 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem4008804 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem4008805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4008806 (m : nat) (n : nat) (p : nat) : (term112 m n p) = (term113 m n p).
Proof. exact (MK_COMB (@lem4008805) (@lem4008803 m n p)). Qed.
Lemma lem4008807 (n : nat) (m : nat) (p : nat) : (term114 n m p) = (term115 n m p).
Proof. exact (MK_COMB (@lem4008806 m n p) (@lem4008804 m p)). Qed.
Lemma lem4008808 (n : nat) (m : nat) (p : nat) : (term48 n m p) = (term114 n m p).
Proof. exact (@lem17265 (term116 m n p) (Peano.le m p)). Qed.
Lemma lem4008809 (n : nat) (m : nat) (p : nat) : (term48 n m p) = (term115 n m p).
Proof. exact (TRANS (@lem4008808 n m p) (@lem4008807 n m p)). Qed.
Lemma lem4008810 (n : nat) (m : nat) : (term49 n m) = (term117 n m).
Proof. exact (fun_ext (fun p : nat => @lem4008809 n m p)). Qed.
Lemma lem4008811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4008812 (n : nat) (m : nat) : (term50 n m) = (term118 n m).
Proof. exact (MK_COMB (@lem4008811) (@lem4008810 n m)). Qed.
Lemma lem4008813 (m : nat) : (term51 m) = (term119 m).
Proof. exact (fun_ext (fun n : nat => @lem4008812 n m)). Qed.
Lemma lem4008814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4008815 (m : nat) : (term52 m) = (term120 m).
Proof. exact (MK_COMB (@lem4008814) (@lem4008813 m)). Qed.
Lemma lem4008816 : term53 = term121.
Proof. exact (fun_ext (fun m : nat => @lem4008815 m)). Qed.
Lemma lem4008817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4008878 : term54 = term122.
Proof. exact (MK_COMB (@lem4008817) (@lem4008816)). Qed.
Lemma lem4008879 (h1 : term54) : term122.
Proof. exact (EQ_MP (@lem4008878) (@lem4008475 h1)). Qed.
Lemma lem4008956 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term44 A B f s) = (term123 A B f s).
Proof. exact (@lem17265 (@FINITE A s) (term124 A B f s)). Qed.
Lemma lem4008957 {A B : Type'} (f : A -> B) : (term45 A B f) = (term125 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4008956 A B f s)). Qed.
Lemma lem4008958 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4008959 {A B : Type'} (f : A -> B) : (term46 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem4008958 A) (@lem4008957 A B f)). Qed.
Lemma lem4008960 {A B : Type'} : (term47 A B) = (term127 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4008959 A B f)). Qed.
Lemma lem4008961 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4009018 {A B : Type'} : (term11 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem4008961 A B) (@lem4008960 A B)). Qed.
Lemma lem4009019 {A B : Type'} (h1 : term11 A B) : term128 A B.
Proof. exact (EQ_MP (@lem4009018 A B) (@lem4008477 A B h1)). Qed.
Lemma lem4009090 {A B : Type'} (f : A -> B) (h1 : term96 A B f) : term96 A B f.
Proof. exact (h1). Qed.
Lemma lem4009091 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term87 A B f s) : term87 A B f s.
Proof. exact (h1). Qed.
Lemma lem4009129 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term105 A B f s) = (term105 A B f s).
Proof. exact (eq_refl (term105 A B f s)). Qed.
Lemma lem4009130 {A B : Type'} (f : A -> B) : (term106 A B f) = (term106 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4009129 A B f s)). Qed.
Lemma lem4009131 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4009132 {A B : Type'} (f : A -> B) : (term107 A B f) = (term107 A B f).
Proof. exact (MK_COMB (@lem4009131 A) (@lem4009130 A B f)). Qed.
Lemma lem4009133 {A B : Type'} : (term108 A B) = (term108 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4009132 A B f)). Qed.
Lemma lem4009134 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4009135 {A B : Type'} : (term109 A B) = (term109 A B).
Proof. exact (MK_COMB (@lem4009134 A B) (@lem4009133 A B)). Qed.
Lemma lem4009136 {A B : Type'} (h1 : term13 A B) : term109 A B.
Proof. exact (EQ_MP (@lem4009135 A B) (@lem4008726 A B h1)). Qed.
Lemma lem4009183 (n : nat) (m : nat) (p : nat) : (term115 n m p) = (term115 n m p).
Proof. exact (eq_refl (term115 n m p)). Qed.
Lemma lem4009184 (n : nat) (m : nat) : (term117 n m) = (term117 n m).
Proof. exact (fun_ext (fun p : nat => @lem4009183 n m p)). Qed.
Lemma lem4009185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4009186 (n : nat) (m : nat) : (term118 n m) = (term118 n m).
Proof. exact (MK_COMB (@lem4009185) (@lem4009184 n m)). Qed.
Lemma lem4009187 (m : nat) : (term119 m) = (term119 m).
Proof. exact (fun_ext (fun n : nat => @lem4009186 n m)). Qed.
Lemma lem4009188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4009189 (m : nat) : (term120 m) = (term120 m).
Proof. exact (MK_COMB (@lem4009188) (@lem4009187 m)). Qed.
Lemma lem4009190 : term121 = term121.
Proof. exact (fun_ext (fun m : nat => @lem4009189 m)). Qed.
Lemma lem4009191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4009192 : term122 = term122.
Proof. exact (MK_COMB (@lem4009191) (@lem4009190)). Qed.
Lemma lem4009193 (h1 : term54) : term122.
Proof. exact (EQ_MP (@lem4009192) (@lem4008879 h1)). Qed.
Lemma lem4009242 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term123 A B f s) = (term123 A B f s).
Proof. exact (eq_refl (term123 A B f s)). Qed.
Lemma lem4009243 {A B : Type'} (f : A -> B) : (term125 A B f) = (term125 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4009242 A B f s)). Qed.
Lemma lem4009244 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4009245 {A B : Type'} (f : A -> B) : (term126 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem4009244 A) (@lem4009243 A B f)). Qed.
Lemma lem4009246 {A B : Type'} : (term127 A B) = (term127 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4009245 A B f)). Qed.
Lemma lem4009247 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4009248 {A B : Type'} : (term128 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem4009247 A B) (@lem4009246 A B)). Qed.
Lemma lem4009249 {A B : Type'} (h1 : term11 A B) : term128 A B.
Proof. exact (EQ_MP (@lem4009248 A B) (@lem4009019 A B h1)). Qed.
Lemma lem4009319 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : term75 A B f s n.
Proof. exact (h1). Qed.
Lemma lem4009320 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : term70 A B f s n.
Proof. exact (proj2 (@lem4009319 A B f s n h1)). Qed.
Lemma lem4009321 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : term77 A s n.
Proof. exact (proj1 (@lem4009319 A B f s n h1)). Qed.
Lemma lem4009349 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term105 A B f s) = (term105 A B f s).
Proof. exact (eq_refl (term105 A B f s)). Qed.
Lemma lem4009350 {A B : Type'} (f : A -> B) : (term106 A B f) = (term106 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4009349 A B f s)). Qed.
Lemma lem4009351 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4009352 {A B : Type'} (f : A -> B) : (term107 A B f) = (term107 A B f).
Proof. exact (MK_COMB (@lem4009351 A) (@lem4009350 A B f)). Qed.
Lemma lem4009353 {A B : Type'} : (term108 A B) = (term108 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4009352 A B f)). Qed.
Lemma lem4009354 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4009356 {A B : Type'} : (term109 A B) = (term109 A B).
Proof. exact (MK_COMB (@lem4009354 A B) (@lem4009353 A B)). Qed.
Lemma lem4009357 {A B : Type'} (h1 : term13 A B) : term109 A B.
Proof. exact (EQ_MP (@lem4009356 A B) (@lem4009136 A B h1)). Qed.
Lemma lem4009458 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term129 A B f s) : term129 A B f s.
Proof. exact (h1). Qed.
Lemma lem4009520 (n : nat) (m : nat) (p : nat) : (term115 n m p) = (term115 n m p).
Proof. exact (eq_refl (term115 n m p)). Qed.
Lemma lem4009521 (n : nat) (m : nat) : (term117 n m) = (term117 n m).
Proof. exact (fun_ext (fun p : nat => @lem4009520 n m p)). Qed.
Lemma lem4009522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4009523 (n : nat) (m : nat) : (term118 n m) = (term118 n m).
Proof. exact (MK_COMB (@lem4009522) (@lem4009521 n m)). Qed.
Lemma lem4009524 (m : nat) : (term119 m) = (term119 m).
Proof. exact (fun_ext (fun n : nat => @lem4009523 n m)). Qed.
Lemma lem4009525 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4009526 (m : nat) : (term120 m) = (term120 m).
Proof. exact (MK_COMB (@lem4009525) (@lem4009524 m)). Qed.
Lemma lem4009527 : term121 = term121.
Proof. exact (fun_ext (fun m : nat => @lem4009526 m)). Qed.
Lemma lem4009528 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4009530 : term122 = term122.
Proof. exact (MK_COMB (@lem4009528) (@lem4009527)). Qed.
Lemma lem4009531 (h1 : term54) : term122.
Proof. exact (EQ_MP (@lem4009530) (@lem4009193 h1)). Qed.
Lemma lem4009555 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term123 A B f s) = (term123 A B f s).
Proof. exact (eq_refl (term123 A B f s)). Qed.
Lemma lem4009556 {A B : Type'} (f : A -> B) : (term125 A B f) = (term125 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4009555 A B f s)). Qed.
Lemma lem4009557 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4009558 {A B : Type'} (f : A -> B) : (term126 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem4009557 A) (@lem4009556 A B f)). Qed.
Lemma lem4009559 {A B : Type'} : (term127 A B) = (term127 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4009558 A B f)). Qed.
Lemma lem4009560 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4009562 {A B : Type'} : (term128 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem4009560 A B) (@lem4009559 A B)). Qed.
Lemma lem4009563 {A B : Type'} (h1 : term11 A B) : term128 A B.
Proof. exact (EQ_MP (@lem4009562 A B) (@lem4009249 A B h1)). Qed.
Lemma lem4009591 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term130 A B f s n) : term130 A B f s n.
Proof. exact (h1). Qed.
Lemma lem4009598 {A B : Type'} (_46272 : A -> B) (h1 : term13 A B) : term131 A B _46272.
Proof. exact (@lem4009357 A B h1 _46272). Qed.
Lemma lem4009599 {A B : Type'} (_46272 : A -> B) : (term131 A B _46272) = (term107 A B _46272).
Proof. exact (eq_refl (term131 A B _46272)). Qed.
Lemma lem4009600 {A B : Type'} (_46272 : A -> B) (h1 : term13 A B) : term107 A B _46272.
Proof. exact (EQ_MP (@lem4009599 A B _46272) (@lem4009598 A B _46272 h1)). Qed.
Lemma lem4009601 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) (h1 : term13 A B) : term132 A B _46272 _46273.
Proof. exact (@lem4009600 A B _46272 h1 _46273). Qed.
Lemma lem4009602 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term132 A B _46272 _46273) = (term105 A B _46272 _46273).
Proof. exact (eq_refl (term132 A B _46272 _46273)). Qed.
Lemma lem4009655 (_46291 : nat) (h1 : term54) : term133 _46291.
Proof. exact (@lem4009531 h1 _46291). Qed.
Lemma lem4009656 (_46291 : nat) : (term133 _46291) = (term120 _46291).
Proof. exact (eq_refl (term133 _46291)). Qed.
Lemma lem4009657 (_46291 : nat) (h1 : term54) : term120 _46291.
Proof. exact (EQ_MP (@lem4009656 _46291) (@lem4009655 _46291 h1)). Qed.
Lemma lem4009658 (_46291 : nat) (_46292 : nat) (h1 : term54) : term134 _46291 _46292.
Proof. exact (@lem4009657 _46291 h1 _46292). Qed.
Lemma lem4009659 (_46292 : nat) (_46291 : nat) : (term134 _46291 _46292) = (term118 _46292 _46291).
Proof. exact (eq_refl (term134 _46291 _46292)). Qed.
Lemma lem4009660 (_46292 : nat) (_46291 : nat) (h1 : term54) : term118 _46292 _46291.
Proof. exact (EQ_MP (@lem4009659 _46292 _46291) (@lem4009658 _46291 _46292 h1)). Qed.
Lemma lem4009661 (_46292 : nat) (_46291 : nat) (_46293 : nat) (h1 : term54) : term135 _46292 _46291 _46293.
Proof. exact (@lem4009660 _46292 _46291 h1 _46293). Qed.
Lemma lem4009662 (_46292 : nat) (_46291 : nat) (_46293 : nat) : (term135 _46292 _46291 _46293) = (term115 _46292 _46291 _46293).
Proof. exact (eq_refl (term135 _46292 _46291 _46293)). Qed.
Lemma lem4009663 (_46292 : nat) (_46291 : nat) (_46293 : nat) (h1 : term54) : term115 _46292 _46291 _46293.
Proof. exact (EQ_MP (@lem4009662 _46292 _46291 _46293) (@lem4009661 _46292 _46291 _46293 h1)). Qed.
Lemma lem4009670 {A B : Type'} (_46296 : A -> B) (h1 : term11 A B) : term136 A B _46296.
Proof. exact (@lem4009563 A B h1 _46296). Qed.
Lemma lem4009671 {A B : Type'} (_46296 : A -> B) : (term136 A B _46296) = (term126 A B _46296).
Proof. exact (eq_refl (term136 A B _46296)). Qed.
Lemma lem4009672 {A B : Type'} (_46296 : A -> B) (h1 : term11 A B) : term126 A B _46296.
Proof. exact (EQ_MP (@lem4009671 A B _46296) (@lem4009670 A B _46296 h1)). Qed.
Lemma lem4009673 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) (h1 : term11 A B) : term137 A B _46296 _46297.
Proof. exact (@lem4009672 A B _46296 h1 _46297). Qed.
Lemma lem4009674 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term137 A B _46296 _46297) = (term123 A B _46296 _46297).
Proof. exact (eq_refl (term137 A B _46296 _46297)). Qed.
Lemma lem4009693 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) (h1 : term13 A B) : term105 A B _46272 _46273.
Proof. exact (EQ_MP (@lem4009602 A B _46272 _46273) (@lem4009601 A B _46272 _46273 h1)). Qed.
Lemma lem4009735 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term129 A B f s) : term129 A B f s.
Proof. exact (h1). Qed.
Lemma lem4009764 (_46292 : nat) (_46291 : nat) (_46293 : nat) : (term115 _46292 _46291 _46293) = (term138 _46292 _46291 _46293).
Proof. exact (@lem4008013 (term139 _46291 _46292) (term139 _46292 _46293) (Peano.le _46291 _46293)). Qed.
Lemma lem4009765 (_46292 : nat) (_46291 : nat) (_46293 : nat) (h1 : term54) : term138 _46292 _46291 _46293.
Proof. exact (EQ_MP (@lem4009764 _46292 _46291 _46293) (@lem4009663 _46292 _46291 _46293 h1)). Qed.
Lemma lem4009777 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) (h1 : term11 A B) : term123 A B _46296 _46297.
Proof. exact (EQ_MP (@lem4009674 A B _46296 _46297) (@lem4009673 A B _46296 _46297 h1)). Qed.
Lemma lem4009789 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term130 A B f s n) : term130 A B f s n.
Proof. exact (h1). Qed.
Lemma lem4009791 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : @FINITE A s.
Proof. exact (proj1 (@lem4009321 A B f s n h1)). Qed.
Lemma lem4009792 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : term140 A s.
Proof. exact (fun h0 : term141 A s => @lem4009791 A B f s n h1). Qed.
Lemma lem4009794 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4009795 {A : Type'} (s : A -> Prop) : (term140 A s) = (@FINITE A s).
Proof. exact (@lem4009794 (@FINITE A s)). Qed.
Lemma lem4009796 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : @FINITE A s.
Proof. exact (EQ_MP (@lem4009795 A s) (@lem4009792 A B f s n h1)). Qed.
Lemma lem4009802 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4009803 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term105 A B _46272 _46273) = (term143 A B _46272 _46273).
Proof. exact (@lem4009802 (term71 A B _46272 _46273) (term141 A _46273)). Qed.
Lemma lem4009809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4009810 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term144 A B _46272 _46273) = (term145 A B _46272 _46273).
Proof. exact (MK_COMB (@lem4009809) (@lem4009803 A B _46272 _46273)). Qed.
Lemma lem4009816 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term143 A B _46272 _46273) = (term143 A B _46272 _46273).
Proof. exact (eq_refl (term143 A B _46272 _46273)). Qed.
Lemma lem4009817 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : ((term105 A B _46272 _46273) = (term143 A B _46272 _46273)) = ((term143 A B _46272 _46273) = (term143 A B _46272 _46273)).
Proof. exact (MK_COMB (@lem4009810 A B _46272 _46273) (@lem4009816 A B _46272 _46273)). Qed.
Lemma lem4009819 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4009820 (x : Prop) : (x = x) = True.
Proof. exact (@lem4009819 Prop x). Qed.
Lemma lem4009821 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : ((term143 A B _46272 _46273) = (term143 A B _46272 _46273)) = True.
Proof. exact (@lem4009820 (term143 A B _46272 _46273)). Qed.
Lemma lem4009822 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : ((term105 A B _46272 _46273) = (term143 A B _46272 _46273)) = True.
Proof. exact (TRANS (@lem4009817 A B _46272 _46273) (@lem4009821 A B _46272 _46273)). Qed.
Lemma lem4009823 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : True = ((term105 A B _46272 _46273) = (term143 A B _46272 _46273)).
Proof. exact (SYM (@lem4009822 A B _46272 _46273)). Qed.
Lemma lem4009824 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term105 A B _46272 _46273) = (term143 A B _46272 _46273).
Proof. exact (EQ_MP (@lem4009823 A B _46272 _46273) (@lem0)). Qed.
Lemma lem4009825 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) (h1 : term13 A B) : term143 A B _46272 _46273.
Proof. exact (EQ_MP (@lem4009824 A B _46272 _46273) (@lem4009693 A B _46272 _46273 h1)). Qed.
Lemma lem4009827 (b : Prop) (a : Prop) : (a \/ b) = (term146 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4009828 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term143 A B _46272 _46273) = (term147 A B _46272 _46273).
Proof. exact (@lem4009827 (term141 A _46273) (term71 A B _46272 _46273)). Qed.
Lemma lem4009830 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4009831 {A : Type'} (_46273 : A -> Prop) : (term149 A _46273) = (@FINITE A _46273).
Proof. exact (@lem4009830 (@FINITE A _46273)). Qed.
Lemma lem4009832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4009833 {A : Type'} (_46273 : A -> Prop) : (term150 A _46273) = (term151 A _46273).
Proof. exact (MK_COMB (@lem4009832) (@lem4009831 A _46273)). Qed.
Lemma lem4009834 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term71 A B _46272 _46273) = (term71 A B _46272 _46273).
Proof. exact (eq_refl (term71 A B _46272 _46273)). Qed.
Lemma lem4009835 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term147 A B _46272 _46273) = (term59 A B _46272 _46273).
Proof. exact (MK_COMB (@lem4009833 A _46273) (@lem4009834 A B _46272 _46273)). Qed.
Lemma lem4009836 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) : (term143 A B _46272 _46273) = (term59 A B _46272 _46273).
Proof. exact (TRANS (@lem4009828 A B _46272 _46273) (@lem4009835 A B _46272 _46273)). Qed.
Lemma lem4009839 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) (h1 : term13 A B) : term59 A B _46272 _46273.
Proof. exact (EQ_MP (@lem4009836 A B _46272 _46273) (@lem4009825 A B _46272 _46273 h1)). Qed.
Lemma lem4009840 {A B : Type'} (_46272 : A -> B) (_46273 : A -> Prop) (h1 : term13 A B) : term59 A B _46272 _46273.
Proof. exact (@lem4009839 A B _46272 _46273 h1). Qed.
Lemma lem4009841 {A B : Type'} (_46272 : A -> B) (s : A -> Prop) (h1 : term13 A B) : term59 A B _46272 s.
Proof. exact (@lem4009840 A B _46272 s h1). Qed.
Lemma lem4009844 {A B : Type'} (_46272 : A -> B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term75 A B f s n) : term71 A B _46272 s.
Proof. exact (@lem4009841 A B _46272 s h1 (@lem4009796 A B f s n h2)). Qed.
Lemma lem4009845 {A B : Type'} (_46272 : A -> B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term75 A B f s n) : term71 A B _46272 s.
Proof. exact (@lem4009844 A B _46272 f s n h1 h2). Qed.
Lemma lem4009846 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term75 A B f s n) : term71 A B f s.
Proof. exact (@lem4009845 A B f f s n h1 h2). Qed.
Lemma lem4009847 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term75 A B f s n) : term152 A B f s.
Proof. exact (fun h0 : term129 A B f s => @lem4009846 A B f s n h1 h2). Qed.
Lemma lem4009849 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4009850 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term152 A B f s) = (term71 A B f s).
Proof. exact (@lem4009849 (term71 A B f s)). Qed.
Lemma lem4009851 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term75 A B f s n) : term71 A B f s.
Proof. exact (EQ_MP (@lem4009850 A B f s) (@lem4009847 A B f s n h1 h2)). Qed.
Lemma lem4009854 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4009856 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term129 A B f s) = (term153 A B f s).
Proof. exact (@lem4009854 (term71 A B f s)). Qed.
Lemma lem4009859 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term129 A B f s) : term153 A B f s.
Proof. exact (EQ_MP (@lem4009856 A B f s) (@lem4009735 A B f s h1)). Qed.
Lemma lem4009862 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : False.
Proof. exact (@lem4009859 A B f s h2 (@lem4009851 A B f s n h1 h3)). Qed.
Lemma lem4009863 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : term154.
Proof. exact (fun h0 : ~ False => @lem4009862 A B f s n h1 h2 h3). Qed.
Lemma lem4009865 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4009866 : term154 = False.
Proof. exact (@lem4009865 False). Qed.
Lemma lem4009867 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4009866) (@lem4009863 A B f s n h1 h2 h3)). Qed.
Lemma lem4009869 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : @FINITE A s.
Proof. exact (proj1 (@lem4009321 A B f s n h1)). Qed.
Lemma lem4009870 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : term140 A s.
Proof. exact (fun h0 : term141 A s => @lem4009869 A B f s n h1). Qed.
Lemma lem4009872 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4009873 {A : Type'} (s : A -> Prop) : (term140 A s) = (@FINITE A s).
Proof. exact (@lem4009872 (@FINITE A s)). Qed.
Lemma lem4009874 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : @FINITE A s.
Proof. exact (EQ_MP (@lem4009873 A s) (@lem4009870 A B f s n h1)). Qed.
Lemma lem4009880 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4009881 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term123 A B _46296 _46297) = (term155 A B _46296 _46297).
Proof. exact (@lem4009880 (term124 A B _46296 _46297) (term141 A _46297)). Qed.
Lemma lem4009887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4009888 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term156 A B _46296 _46297) = (term157 A B _46296 _46297).
Proof. exact (MK_COMB (@lem4009887) (@lem4009881 A B _46296 _46297)). Qed.
Lemma lem4009894 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term155 A B _46296 _46297) = (term155 A B _46296 _46297).
Proof. exact (eq_refl (term155 A B _46296 _46297)). Qed.
Lemma lem4009895 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : ((term123 A B _46296 _46297) = (term155 A B _46296 _46297)) = ((term155 A B _46296 _46297) = (term155 A B _46296 _46297)).
Proof. exact (MK_COMB (@lem4009888 A B _46296 _46297) (@lem4009894 A B _46296 _46297)). Qed.
Lemma lem4009897 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4009898 (x : Prop) : (x = x) = True.
Proof. exact (@lem4009897 Prop x). Qed.
Lemma lem4009899 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : ((term155 A B _46296 _46297) = (term155 A B _46296 _46297)) = True.
Proof. exact (@lem4009898 (term155 A B _46296 _46297)). Qed.
Lemma lem4009900 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : ((term123 A B _46296 _46297) = (term155 A B _46296 _46297)) = True.
Proof. exact (TRANS (@lem4009895 A B _46296 _46297) (@lem4009899 A B _46296 _46297)). Qed.
Lemma lem4009901 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : True = ((term123 A B _46296 _46297) = (term155 A B _46296 _46297)).
Proof. exact (SYM (@lem4009900 A B _46296 _46297)). Qed.
Lemma lem4009902 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term123 A B _46296 _46297) = (term155 A B _46296 _46297).
Proof. exact (EQ_MP (@lem4009901 A B _46296 _46297) (@lem0)). Qed.
Lemma lem4009903 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) (h1 : term11 A B) : term155 A B _46296 _46297.
Proof. exact (EQ_MP (@lem4009902 A B _46296 _46297) (@lem4009777 A B _46296 _46297 h1)). Qed.
Lemma lem4009905 (b : Prop) (a : Prop) : (a \/ b) = (term146 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4009906 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term155 A B _46296 _46297) = (term158 A B _46296 _46297).
Proof. exact (@lem4009905 (term141 A _46297) (term124 A B _46296 _46297)). Qed.
Lemma lem4009908 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4009909 {A : Type'} (_46297 : A -> Prop) : (term149 A _46297) = (@FINITE A _46297).
Proof. exact (@lem4009908 (@FINITE A _46297)). Qed.
Lemma lem4009910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4009911 {A : Type'} (_46297 : A -> Prop) : (term150 A _46297) = (term151 A _46297).
Proof. exact (MK_COMB (@lem4009910) (@lem4009909 A _46297)). Qed.
Lemma lem4009912 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term124 A B _46296 _46297) = (term124 A B _46296 _46297).
Proof. exact (eq_refl (term124 A B _46296 _46297)). Qed.
Lemma lem4009913 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term158 A B _46296 _46297) = (term44 A B _46296 _46297).
Proof. exact (MK_COMB (@lem4009911 A _46297) (@lem4009912 A B _46296 _46297)). Qed.
Lemma lem4009914 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) : (term155 A B _46296 _46297) = (term44 A B _46296 _46297).
Proof. exact (TRANS (@lem4009906 A B _46296 _46297) (@lem4009913 A B _46296 _46297)). Qed.
Lemma lem4009917 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) (h1 : term11 A B) : term44 A B _46296 _46297.
Proof. exact (EQ_MP (@lem4009914 A B _46296 _46297) (@lem4009903 A B _46296 _46297 h1)). Qed.
Lemma lem4009918 {A B : Type'} (_46296 : A -> B) (_46297 : A -> Prop) (h1 : term11 A B) : term44 A B _46296 _46297.
Proof. exact (@lem4009917 A B _46296 _46297 h1). Qed.
Lemma lem4009919 {A B : Type'} (_46296 : A -> B) (s : A -> Prop) (h1 : term11 A B) : term44 A B _46296 s.
Proof. exact (@lem4009918 A B _46296 s h1). Qed.
Lemma lem4009922 {A B : Type'} (_46296 : A -> B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term75 A B f s n) : term124 A B _46296 s.
Proof. exact (@lem4009919 A B _46296 s h1 (@lem4009874 A B f s n h2)). Qed.
Lemma lem4009923 {A B : Type'} (_46296 : A -> B) (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term75 A B f s n) : term124 A B _46296 s.
Proof. exact (@lem4009922 A B _46296 f s n h1 h2). Qed.
Lemma lem4009924 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term75 A B f s n) : term124 A B f s.
Proof. exact (@lem4009923 A B f f s n h1 h2). Qed.
Lemma lem4009925 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term75 A B f s n) : term159 A B f s.
Proof. exact (fun h0 : term160 A B f s => @lem4009924 A B f s n h1 h2). Qed.
Lemma lem4009927 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4009928 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term159 A B f s) = (term124 A B f s).
Proof. exact (@lem4009927 (term124 A B f s)). Qed.
Lemma lem4009929 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term75 A B f s n) : term124 A B f s.
Proof. exact (EQ_MP (@lem4009928 A B f s) (@lem4009925 A B f s n h1 h2)). Qed.
Lemma lem4009931 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : term161 A s n.
Proof. exact (proj2 (@lem4009321 A B f s n h1)). Qed.
Lemma lem4009932 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : term162 A s n.
Proof. exact (fun h0 : term163 A s n => @lem4009931 A B f s n h1). Qed.
Lemma lem4009934 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4009935 {A : Type'} (s : A -> Prop) (n : nat) : (term162 A s n) = (term161 A s n).
Proof. exact (@lem4009934 (term161 A s n)). Qed.
Lemma lem4009936 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term75 A B f s n) : term161 A s n.
Proof. exact (EQ_MP (@lem4009935 A s n) (@lem4009932 A B f s n h1)). Qed.
Lemma lem4009952 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4009953 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term164 _46292 _46291 _46293) = (term165 _46291 _46292 _46293).
Proof. exact (@lem4009952 (Peano.le _46291 _46293) (term139 _46292 _46293)). Qed.
Lemma lem4009959 (_46291 : nat) (_46292 : nat) : (term166 _46291 _46292) = (term166 _46291 _46292).
Proof. exact (eq_refl (term166 _46291 _46292)). Qed.
Lemma lem4009960 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term138 _46292 _46291 _46293) = (term167 _46291 _46292 _46293).
Proof. exact (MK_COMB (@lem4009959 _46291 _46292) (@lem4009953 _46291 _46292 _46293)). Qed.
Lemma lem4009964 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4009965 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term167 _46291 _46292 _46293) = (term168 _46291 _46292 _46293).
Proof. exact (@lem4009964 (Peano.le _46291 _46293) (term139 _46291 _46292) (term139 _46292 _46293)). Qed.
Lemma lem4009981 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term138 _46292 _46291 _46293) = (term168 _46291 _46292 _46293).
Proof. exact (TRANS (@lem4009960 _46291 _46292 _46293) (@lem4009965 _46291 _46292 _46293)). Qed.
Lemma lem4009982 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4009983 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term169 _46292 _46291 _46293) = (term170 _46291 _46292 _46293).
Proof. exact (MK_COMB (@lem4009982) (@lem4009981 _46291 _46292 _46293)). Qed.
Lemma lem4009999 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term168 _46291 _46292 _46293) = (term168 _46291 _46292 _46293).
Proof. exact (eq_refl (term168 _46291 _46292 _46293)). Qed.
Lemma lem4010000 (_46291 : nat) (_46292 : nat) (_46293 : nat) : ((term138 _46292 _46291 _46293) = (term168 _46291 _46292 _46293)) = ((term168 _46291 _46292 _46293) = (term168 _46291 _46292 _46293)).
Proof. exact (MK_COMB (@lem4009983 _46291 _46292 _46293) (@lem4009999 _46291 _46292 _46293)). Qed.
Lemma lem4010002 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4010003 (x : Prop) : (x = x) = True.
Proof. exact (@lem4010002 Prop x). Qed.
Lemma lem4010004 (_46291 : nat) (_46292 : nat) (_46293 : nat) : ((term168 _46291 _46292 _46293) = (term168 _46291 _46292 _46293)) = True.
Proof. exact (@lem4010003 (term168 _46291 _46292 _46293)). Qed.
Lemma lem4010005 (_46291 : nat) (_46292 : nat) (_46293 : nat) : ((term138 _46292 _46291 _46293) = (term168 _46291 _46292 _46293)) = True.
Proof. exact (TRANS (@lem4010000 _46291 _46292 _46293) (@lem4010004 _46291 _46292 _46293)). Qed.
Lemma lem4010006 (_46291 : nat) (_46292 : nat) (_46293 : nat) : True = ((term138 _46292 _46291 _46293) = (term168 _46291 _46292 _46293)).
Proof. exact (SYM (@lem4010005 _46291 _46292 _46293)). Qed.
Lemma lem4010007 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term138 _46292 _46291 _46293) = (term168 _46291 _46292 _46293).
Proof. exact (EQ_MP (@lem4010006 _46291 _46292 _46293) (@lem0)). Qed.
Lemma lem4010008 (_46291 : nat) (_46292 : nat) (_46293 : nat) (h1 : term54) : term168 _46291 _46292 _46293.
Proof. exact (EQ_MP (@lem4010007 _46291 _46292 _46293) (@lem4009765 _46292 _46291 _46293 h1)). Qed.
Lemma lem4010010 (b : Prop) (a : Prop) : (a \/ b) = (term146 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4010011 (_46292 : nat) (_46291 : nat) (_46293 : nat) : (term168 _46291 _46292 _46293) = (term171 _46292 _46291 _46293).
Proof. exact (@lem4010010 (term111 _46291 _46292 _46293) (Peano.le _46291 _46293)). Qed.
Lemma lem4010013 (a : Prop) (b : Prop) : (term172 a b) = (term173 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4010014 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term174 _46291 _46292 _46293) = (term175 _46291 _46292 _46293).
Proof. exact (@lem4010013 (term139 _46291 _46292) (term139 _46292 _46293)). Qed.
Lemma lem4010016 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4010017 (_46291 : nat) (_46292 : nat) : (term176 _46291 _46292) = (Peano.le _46291 _46292).
Proof. exact (@lem4010016 (Peano.le _46291 _46292)). Qed.
Lemma lem4010018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4010019 (_46291 : nat) (_46292 : nat) : (term177 _46291 _46292) = (term178 _46291 _46292).
Proof. exact (MK_COMB (@lem4010018) (@lem4010017 _46291 _46292)). Qed.
Lemma lem4010021 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4010022 (_46292 : nat) (_46293 : nat) : (term176 _46292 _46293) = (Peano.le _46292 _46293).
Proof. exact (@lem4010021 (Peano.le _46292 _46293)). Qed.
Lemma lem4010023 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term175 _46291 _46292 _46293) = (term116 _46291 _46292 _46293).
Proof. exact (MK_COMB (@lem4010019 _46291 _46292) (@lem4010022 _46292 _46293)). Qed.
Lemma lem4010024 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term174 _46291 _46292 _46293) = (term116 _46291 _46292 _46293).
Proof. exact (TRANS (@lem4010014 _46291 _46292 _46293) (@lem4010023 _46291 _46292 _46293)). Qed.
Lemma lem4010025 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4010026 (_46291 : nat) (_46292 : nat) (_46293 : nat) : (term179 _46291 _46292 _46293) = (term180 _46291 _46292 _46293).
Proof. exact (MK_COMB (@lem4010025) (@lem4010024 _46291 _46292 _46293)). Qed.
Lemma lem4010027 (_46291 : nat) (_46293 : nat) : (Peano.le _46291 _46293) = (Peano.le _46291 _46293).
Proof. exact (eq_refl (Peano.le _46291 _46293)). Qed.
Lemma lem4010028 (_46292 : nat) (_46291 : nat) (_46293 : nat) : (term171 _46292 _46291 _46293) = (term48 _46292 _46291 _46293).
Proof. exact (MK_COMB (@lem4010026 _46291 _46292 _46293) (@lem4010027 _46291 _46293)). Qed.
Lemma lem4010029 (_46292 : nat) (_46291 : nat) (_46293 : nat) : (term168 _46291 _46292 _46293) = (term48 _46292 _46291 _46293).
Proof. exact (TRANS (@lem4010011 _46292 _46291 _46293) (@lem4010028 _46292 _46291 _46293)). Qed.
Lemma lem4010031 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term75 A B f s n) : term181 A B f s n.
Proof. exact (conj (@lem4009929 A B f s n h1 h2) (@lem4009936 A B f s n h2)). Qed.
Lemma lem4010033 (_46292 : nat) (_46291 : nat) (_46293 : nat) (h1 : term54) : term48 _46292 _46291 _46293.
Proof. exact (EQ_MP (@lem4010029 _46292 _46291 _46293) (@lem4010008 _46291 _46292 _46293 h1)). Qed.
Lemma lem4010034 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term54) : term182 A B f s n.
Proof. exact (@lem4010033 (@CARD A s) (term183 A B f s) n h1). Qed.
Lemma lem4010037 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term75 A B f s n) : term72 A B f s n.
Proof. exact (@lem4010034 A B f s n h2 (@lem4010031 A B f s n h1 h3)). Qed.
Lemma lem4010038 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term75 A B f s n) : term184 A B f s n.
Proof. exact (fun h0 : term130 A B f s n => @lem4010037 A B f s n h1 h2 h3). Qed.
Lemma lem4010040 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4010041 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term184 A B f s n) = (term72 A B f s n).
Proof. exact (@lem4010040 (term72 A B f s n)). Qed.
Lemma lem4010042 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term75 A B f s n) : term72 A B f s n.
Proof. exact (EQ_MP (@lem4010041 A B f s n) (@lem4010038 A B f s n h1 h2 h3)). Qed.
Lemma lem4010045 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4010047 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term130 A B f s n) = (term185 A B f s n).
Proof. exact (@lem4010045 (term72 A B f s n)). Qed.
Lemma lem4010050 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term130 A B f s n) : term185 A B f s n.
Proof. exact (EQ_MP (@lem4010047 A B f s n) (@lem4009789 A B f s n h1)). Qed.
Lemma lem4010053 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : False.
Proof. exact (@lem4010050 A B f s n h3 (@lem4010042 A B f s n h1 h2 h4)). Qed.
Lemma lem4010054 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : term154.
Proof. exact (fun h0 : ~ False => @lem4010053 A B f s n h1 h2 h3 h4). Qed.
Lemma lem4010056 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4010057 : term154 = False.
Proof. exact (@lem4010056 False). Qed.
Lemma lem4010058 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4010057) (@lem4010054 A B f s n h1 h2 h3 h4)). Qed.
Lemma lem4010059 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : (term130 A B f s n) = False.
Proof. exact (prop_ext (fun h5 : term130 A B f s n => @lem4010058 A B f s n h1 h2 h3 h4) (fun h5 : False => @lem4009789 A B f s n h3)). Qed.
Lemma lem4010060 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4010059 A B f s n h1 h2 h3 h4) (@lem4009789 A B f s n h3)). Qed.
Lemma lem4010061 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : (term129 A B f s) = False.
Proof. exact (prop_ext (fun h4 : term129 A B f s => @lem4009867 A B f s n h1 h2 h3) (fun h4 : False => @lem4009735 A B f s h2)). Qed.
Lemma lem4010062 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4010061 A B f s n h1 h2 h3) (@lem4009735 A B f s h2)). Qed.
Lemma lem4010063 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : (term130 A B f s n) = False.
Proof. exact (prop_ext (fun h5 : term130 A B f s n => @lem4010060 A B f s n h1 h2 h3 h4) (fun h5 : False => @lem4009591 A B f s n h3)). Qed.
Lemma lem4010064 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4010063 A B f s n h1 h2 h3 h4) (@lem4009591 A B f s n h3)). Qed.
Lemma lem4010065 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : (term129 A B f s) = False.
Proof. exact (prop_ext (fun h4 : term129 A B f s => @lem4010062 A B f s n h1 h2 h3) (fun h4 : False => @lem4009458 A B f s h2)). Qed.
Lemma lem4010066 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4010065 A B f s n h1 h2 h3) (@lem4009458 A B f s h2)). Qed.
Lemma lem4010067 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : (term130 A B f s n) = False.
Proof. exact (prop_ext (fun h5 : term130 A B f s n => @lem4010064 A B f s n h1 h2 h3 h4) (fun h5 : False => @lem4009591 A B f s n h3)). Qed.
Lemma lem4010068 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term11 A B) (h2 : term54) (h3 : term130 A B f s n) (h4 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4010067 A B f s n h1 h2 h3 h4) (@lem4009591 A B f s n h3)). Qed.
Lemma lem4010069 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : (term129 A B f s) = False.
Proof. exact (prop_ext (fun h4 : term129 A B f s => @lem4010066 A B f s n h1 h2 h3) (fun h4 : False => @lem4009458 A B f s h2)). Qed.
Lemma lem4010070 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term129 A B f s) (h3 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4010069 A B f s n h1 h2 h3) (@lem4009458 A B f s h2)). Qed.
Lemma lem4010071 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term11 A B) (h3 : term54) (h4 : term75 A B f s n) : False.
Proof. exact (or_elim (@lem4009320 A B f s n h4) (fun h0 : term129 A B f s => @lem4010070 A B f s n h1 h0 h4) (fun h0 : term130 A B f s n => @lem4010068 A B f s n h2 h3 h0 h4)). Qed.
Lemma lem4010072 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term11 A B) (h3 : term54) (h4 : term75 A B f s n) : (term75 A B f s n) = False.
Proof. exact (prop_ext (fun h5 : term75 A B f s n => @lem4010071 A B f s n h1 h2 h3 h4) (fun h5 : False => @lem4009319 A B f s n h4)). Qed.
Lemma lem4010073 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term13 A B) (h2 : term11 A B) (h3 : term54) (h4 : term75 A B f s n) : False.
Proof. exact (EQ_MP (@lem4010072 A B f s n h1 h2 h3 h4) (@lem4009319 A B f s n h4)). Qed.
Lemma lem4010074 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term13 A B) (h2 : term11 A B) (h3 : term54) (h4 : term87 A B f s) : False.
Proof. exact (ex_elim (@lem4009091 A B f s h4) (fun n : nat => fun h0 : term86 A B f s n => @lem4010073 A B f s n h1 h2 h3 h0)). Qed.
Lemma lem4010075 {A B : Type'} (f : A -> B) (h1 : term13 A B) (h2 : term11 A B) (h3 : term54) (h4 : term96 A B f) : False.
Proof. exact (ex_elim (@lem4009090 A B f h4) (fun s : A -> Prop => fun h0 : term95 A B f s => @lem4010074 A B f s h1 h2 h3 h0)). Qed.
Lemma lem4010076 {A B : Type'} (h1 : term13 A B) (h2 : term11 A B) (h3 : term54) (h4 : term10 A B) : False.
Proof. exact (ex_elim (@lem4008586 A B h4) (fun f : A -> B => fun h0 : term103 A B f => @lem4010075 A B f h1 h2 h3 h0)). Qed.
Lemma lem4010077 {A B : Type'} (h1 : term13 A B) (h2 : term11 A B) (h3 : term54) (h4 : term10 A B) : term19 B.
Proof. exact (fun h0 : term12 B => @lem4010076 A B h1 h2 h3 h4). Qed.
Lemma lem4010078 {B : Type'} : (term19 B) = (term20 B).
Proof. exact (@lem69 (term12 B)). Qed.
Lemma lem4010079 {A B : Type'} (h1 : term13 A B) (h2 : term11 A B) (h3 : term54) (h4 : term10 A B) : term20 B.
Proof. exact (EQ_MP (@lem4010078 B) (@lem4010077 A B h1 h2 h3 h4)). Qed.
Lemma lem4010080 {A B : Type'} (h1 : term13 A B) (h2 : term54) (h3 : term10 A B) : term23 A B.
Proof. exact (fun h0 : term11 A B => @lem4010079 A B h1 h0 h2 h3). Qed.
Lemma lem4010081 {A B : Type'} (h1 : term13 A B) (h2 : term54) (h3 : term10 A B) : term26 A B.
Proof. exact (fun h0 : term12 A => @lem4010080 A B h1 h2 h3). Qed.
Lemma lem4010082 {A B : Type'} (h1 : term13 A B) (h2 : term10 A B) : term29 A B.
Proof. exact (fun h0 : term54 => @lem4010081 A B h1 h0 h2). Qed.
Lemma lem4010083 {A B : Type'} (h1 : term13 A B) (h2 : term10 A B) : term32 A B.
Proof. exact (fun h0 : term14 B => @lem4010082 A B h1 h2). Qed.
Lemma lem4010084 {A B : Type'} (h1 : term10 A B) : term35 A B.
Proof. exact (fun h0 : term13 A B => @lem4010083 A B h0 h1). Qed.
Lemma lem4010085 {A B : Type'} (h1 : term10 A B) : term37 A B.
Proof. exact (fun h0 : term14 A => @lem4010084 A B h1). Qed.
Lemma lem4010086 {A B : Type'} : term39 A B.
Proof. exact (fun h0 : term10 A B => @lem4010085 A B h0). Qed.
Lemma lem4010087 {A B : Type'} : term15 A B.
Proof. exact (EQ_MP (@lem4008470 A B) (@lem4010086 A B)). Qed.
Lemma lem4010089 {A B : Type'} : term15 A B.
Proof. exact (@lem4008048 A B (@lem4010087 A B)). Qed.
Lemma lem4010090 {A B : Type'} (h1 : term10 A B) : term36 A B.
Proof. exact (@lem4010089 A B (@lem4008018 A B h1)). Qed.
Lemma lem4010091 {A B : Type'} (h1 : term10 A B) : term34 A B.
Proof. exact (@lem4010090 A B h1 (@lem4008028 A)). Qed.
Lemma lem4010092 {A B : Type'} (h1 : term10 A B) : term31 A B.
Proof. exact (@lem4010091 A B h1 (@lem4008026 A B)). Qed.
Lemma lem4010093 {A B : Type'} (h1 : term10 A B) : term28 A B.
Proof. exact (@lem4010092 A B h1 (@lem4008027 B)). Qed.
Lemma lem4010094 {A B : Type'} (h1 : term10 A B) : term25 A B.
Proof. exact (@lem4010093 A B h1 (@lem93743)). Qed.
Lemma lem4010095 {A B : Type'} (h1 : term10 A B) : term22 A B.
Proof. exact (@lem4010094 A B h1 (@lem4008021 A)). Qed.
Lemma lem4010096 {A B : Type'} (h1 : term10 A B) : term19 B.
Proof. exact (@lem4010095 A B h1 (@lem4008019 A B)). Qed.
Lemma lem4010097 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (@lem4010096 A B h1 (@lem4008020 B)). Qed.
Lemma lem4010098 {A B : Type'} (h1 : term10 A B) : (term10 A B) = False.
Proof. exact (prop_ext (fun h2 : term10 A B => @lem4010097 A B h1) (fun h2 : False => @lem4008018 A B h1)). Qed.
Lemma lem4010099 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (EQ_MP (@lem4010098 A B h1) (@lem4008018 A B h1)). Qed.
Lemma lem4010100 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term10 A B => @lem4010099 A B h0). Qed.
Lemma lem4010101 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem4008017 A B) (@lem4010100 A B)). Qed.
