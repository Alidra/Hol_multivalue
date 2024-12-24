Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184689_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3183586_spec.
Lemma lem3184139 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3184140 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term1 _83152 p x) = (p x)) = (term2 _83152 p x).
Proof. exact (@lem3184139 ((term1 _83152 p x) = (p x))). Qed.
Lemma lem3184141 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term2 _83152 p x) = ((term1 _83152 p x) = (p x)).
Proof. exact (SYM (@lem3184140 _83152 p x)). Qed.
Lemma lem3184142 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : term3 _83152 p x.
Proof. exact (h1). Qed.
Lemma lem3184145 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term2 _83152 p x) : term2 _83152 p x.
Proof. exact (h1). Qed.
Lemma lem3184146 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term4 _83152 p x.
Proof. exact (fun h0 : term2 _83152 p x => @lem3184145 _83152 p x h0). Qed.
Lemma lem3184147 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term4 _83152 p x) : term4 _83152 p x.
Proof. exact (h1). Qed.
Lemma lem3184148 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term2 _83152 p x) : term2 _83152 p x.
Proof. exact (h1). Qed.
Lemma lem3184149 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term2 _83152 p x) (h2 : term4 _83152 p x) : term2 _83152 p x.
Proof. exact (@lem3184147 _83152 p x h2 (@lem3184148 _83152 p x h1)). Qed.
Lemma lem3184150 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term2 _83152 p x) : term5 _83152 p x.
Proof. exact (fun h0 : term4 _83152 p x => @lem3184149 _83152 p x h1 h0). Qed.
Lemma lem3184151 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term4 _83152 p x) : term4 _83152 p x.
Proof. exact (h1). Qed.
Lemma lem3184152 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term2 _83152 p x) (h2 : term4 _83152 p x) : term2 _83152 p x.
Proof. exact (@lem3184150 _83152 p x h1 (@lem3184151 _83152 p x h2)). Qed.
Lemma lem3184153 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term4 _83152 p x) : term4 _83152 p x.
Proof. exact (fun h0 : term2 _83152 p x => @lem3184152 _83152 p x h0 h1). Qed.
Lemma lem3184154 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term6 _83152 p x.
Proof. exact (fun h0 : term4 _83152 p x => @lem3184153 _83152 p x h0). Qed.
Lemma lem3184157 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term4 _83152 p x.
Proof. exact (@lem3184154 _83152 p x (@lem3184146 _83152 p x)). Qed.
Lemma lem3184158 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term4 _83152 p x.
Proof. exact (@lem3184157 _83152 p x). Qed.
Lemma lem3184168 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3184169 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term2 _83152 p x) = (term7 _83152 p x).
Proof. exact (@lem3184168 (term3 _83152 p x)). Qed.
Lemma lem3184171 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3184172 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term7 _83152 p x) = ((term1 _83152 p x) = (p x)).
Proof. exact (@lem3184171 ((term1 _83152 p x) = (p x))). Qed.
Lemma lem3184173 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term2 _83152 p x) = ((term1 _83152 p x) = (p x)).
Proof. exact (TRANS (@lem3184169 _83152 p x) (@lem3184172 _83152 p x)). Qed.
Lemma lem3184204 {_83152 : Type'} (x : _83152) : (term9 _83152 x) = (term10 _83152 x).
Proof. exact (fun_ext (fun p : _83152 -> Prop => @lem3184173 _83152 p x)). Qed.
Lemma lem3184205 {_83152 : Type'} : (@all (_83152 -> Prop)) = (@all (_83152 -> Prop)).
Proof. exact (eq_refl (@all (_83152 -> Prop))). Qed.
Lemma lem3184206 {_83152 : Type'} (x : _83152) : (term11 _83152 x) = (term12 _83152 x).
Proof. exact (MK_COMB (@lem3184205 _83152) (@lem3184204 _83152 x)). Qed.
Lemma lem3184211 {_83152 : Type'} : (term13 _83152) = (term14 _83152).
Proof. exact (fun_ext (fun x : _83152 => @lem3184206 _83152 x)). Qed.
Lemma lem3184212 {_83152 : Type'} : (@all _83152) = (@all _83152).
Proof. exact (eq_refl (@all _83152)). Qed.
Lemma lem3184221 {_83152 : Type'} : (term15 _83152) = (term16 _83152).
Proof. exact (MK_COMB (@lem3184212 _83152) (@lem3184211 _83152)). Qed.
Lemma lem3184222 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3184227 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term17 _83152 p x y) = (term17 _83152 p x y).
Proof. exact (eq_refl (term17 _83152 p x y)). Qed.
Lemma lem3184228 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term18 _83152 p x) = (term18 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184227 _83152 p x y)). Qed.
Lemma lem3184229 {_83152 : Type'} : (@ex _83152) = (@ex _83152).
Proof. exact (eq_refl (@ex _83152)). Qed.
Lemma lem3184230 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term1 _83152 p x) = (term1 _83152 p x).
Proof. exact (MK_COMB (@lem3184229 _83152) (@lem3184228 _83152 p x)). Qed.
Lemma lem3184231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3184232 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term19 _83152 p x) = (term19 _83152 p x).
Proof. exact (MK_COMB (@lem3184231) (@lem3184230 _83152 p x)). Qed.
Lemma lem3184233 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term1 _83152 p x) = (p x)) = ((term1 _83152 p x) = (p x)).
Proof. exact (MK_COMB (@lem3184232 _83152 p x) (@lem3184222 _83152 p x)). Qed.
Lemma lem3184234 {_83152 : Type'} (x : _83152) : (term10 _83152 x) = (term10 _83152 x).
Proof. exact (fun_ext (fun p : _83152 -> Prop => @lem3184233 _83152 p x)). Qed.
Lemma lem3184235 {_83152 : Type'} : (@all (_83152 -> Prop)) = (@all (_83152 -> Prop)).
Proof. exact (eq_refl (@all (_83152 -> Prop))). Qed.
Lemma lem3184236 {_83152 : Type'} (x : _83152) : (term12 _83152 x) = (term12 _83152 x).
Proof. exact (MK_COMB (@lem3184235 _83152) (@lem3184234 _83152 x)). Qed.
Lemma lem3184237 {_83152 : Type'} : (term14 _83152) = (term14 _83152).
Proof. exact (fun_ext (fun x : _83152 => @lem3184236 _83152 x)). Qed.
Lemma lem3184238 {_83152 : Type'} : (@all _83152) = (@all _83152).
Proof. exact (eq_refl (@all _83152)). Qed.
Lemma lem3184239 {_83152 : Type'} : (term16 _83152) = (term16 _83152).
Proof. exact (MK_COMB (@lem3184238 _83152) (@lem3184237 _83152)). Qed.
Lemma lem3184262 {_83152 : Type'} : (term15 _83152) = (term16 _83152).
Proof. exact (TRANS (@lem3184221 _83152) (@lem3184239 _83152)). Qed.
Lemma lem3184263 {_83152 : Type'} : (term16 _83152) = (term15 _83152).
Proof. exact (SYM (@lem3184262 _83152)). Qed.
Lemma lem3184265 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3184266 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term1 _83152 p x) = (p x)) = (term2 _83152 p x).
Proof. exact (@lem3184265 ((term1 _83152 p x) = (p x))). Qed.
Lemma lem3184267 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term2 _83152 p x) = ((term1 _83152 p x) = (p x)).
Proof. exact (SYM (@lem3184266 _83152 p x)). Qed.
Lemma lem3184268 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : term3 _83152 p x.
Proof. exact (h1). Qed.
Lemma lem3184277 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term20 _83152 p x y) = (term21 _83152 p x y).
Proof. exact (@lem17045 (p y) (x = y)). Qed.
Lemma lem3184280 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term17 _83152 p x y) = (term17 _83152 p x y).
Proof. exact (eq_refl (term17 _83152 p x y)). Qed.
Lemma lem3184281 {_83152 : Type'} (P : _83152 -> Prop) : (term22 _83152 P) = (term23 _83152 P).
Proof. exact (@lem18394 _83152 P). Qed.
Lemma lem3184282 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term24 _83152 p x) = (term25 _83152 p x).
Proof. exact (@lem3184281 _83152 (term18 _83152 p x)). Qed.
Lemma lem3184283 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term26 _83152 p x y) = (term17 _83152 p x y).
Proof. exact (eq_refl (term26 _83152 p x y)). Qed.
Lemma lem3184284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3184285 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term27 _83152 p x y) = (term20 _83152 p x y).
Proof. exact (MK_COMB (@lem3184284) (@lem3184283 _83152 p x y)). Qed.
Lemma lem3184286 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term27 _83152 p x y) = (term21 _83152 p x y).
Proof. exact (TRANS (@lem3184285 _83152 p x y) (@lem3184277 _83152 p x y)). Qed.
Lemma lem3184287 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term28 _83152 p x) = (term29 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184286 _83152 p x y)). Qed.
Lemma lem3184288 {_83152 : Type'} : (@all _83152) = (@all _83152).
Proof. exact (eq_refl (@all _83152)). Qed.
Lemma lem3184289 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term25 _83152 p x) = (term30 _83152 p x).
Proof. exact (MK_COMB (@lem3184288 _83152) (@lem3184287 _83152 p x)). Qed.
Lemma lem3184290 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term24 _83152 p x) = (term30 _83152 p x).
Proof. exact (TRANS (@lem3184282 _83152 p x) (@lem3184289 _83152 p x)). Qed.
Lemma lem3184291 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term18 _83152 p x) = (term18 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184280 _83152 p x y)). Qed.
Lemma lem3184292 {_83152 : Type'} : (@ex _83152) = (@ex _83152).
Proof. exact (eq_refl (@ex _83152)). Qed.
Lemma lem3184293 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term1 _83152 p x) = (term1 _83152 p x).
Proof. exact (MK_COMB (@lem3184292 _83152) (@lem3184291 _83152 p x)). Qed.
Lemma lem3184294 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term31 _83152 p x) = (term31 _83152 p x).
Proof. exact (eq_refl (term31 _83152 p x)). Qed.
Lemma lem3184295 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3184296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3184297 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term32 _83152 p x) = (term33 _83152 p x).
Proof. exact (MK_COMB (@lem3184296) (@lem3184290 _83152 p x)). Qed.
Lemma lem3184298 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term34 _83152 p x) = (term35 _83152 p x).
Proof. exact (MK_COMB (@lem3184297 _83152 p x) (@lem3184295 _83152 p x)). Qed.
Lemma lem3184299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3184300 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term36 _83152 p x) = (term36 _83152 p x).
Proof. exact (MK_COMB (@lem3184299) (@lem3184293 _83152 p x)). Qed.
Lemma lem3184301 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term37 _83152 p x) = (term37 _83152 p x).
Proof. exact (MK_COMB (@lem3184300 _83152 p x) (@lem3184294 _83152 p x)). Qed.
Lemma lem3184302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3184303 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term38 _83152 p x) = (term38 _83152 p x).
Proof. exact (MK_COMB (@lem3184302) (@lem3184301 _83152 p x)). Qed.
Lemma lem3184304 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term39 _83152 p x) = (term40 _83152 p x).
Proof. exact (MK_COMB (@lem3184303 _83152 p x) (@lem3184298 _83152 p x)). Qed.
Lemma lem3184305 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = (term39 _83152 p x).
Proof. exact (@lem17646 (term1 _83152 p x) (p x)). Qed.
Lemma lem3184306 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = (term40 _83152 p x).
Proof. exact (TRANS (@lem3184305 _83152 p x) (@lem3184304 _83152 p x)). Qed.
Lemma lem3184385 {A : Type'} (P : A -> Prop) (Q : Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3184386 {_83152 : Type'} (P : _83152 -> Prop) (Q : Prop) : (term41 _83152 P Q) = (term42 _83152 P Q).
Proof. exact (@lem3184385 _83152 P Q). Qed.
Lemma lem3184387 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term43 _83152 p x) = (term44 _83152 p x).
Proof. exact (@lem3184386 _83152 (term18 _83152 p x) (term31 _83152 p x)). Qed.
Lemma lem3184388 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term26 _83152 p x y) = (term17 _83152 p x y).
Proof. exact (eq_refl (term26 _83152 p x y)). Qed.
Lemma lem3184389 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term45 _83152 p x) = (term18 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184388 _83152 p x y)). Qed.
Lemma lem3184390 {_83152 : Type'} : (@ex _83152) = (@ex _83152).
Proof. exact (eq_refl (@ex _83152)). Qed.
Lemma lem3184391 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term46 _83152 p x) = (term1 _83152 p x).
Proof. exact (MK_COMB (@lem3184390 _83152) (@lem3184389 _83152 p x)). Qed.
Lemma lem3184392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3184393 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term47 _83152 p x) = (term36 _83152 p x).
Proof. exact (MK_COMB (@lem3184392) (@lem3184391 _83152 p x)). Qed.
Lemma lem3184394 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term31 _83152 p x) = (term31 _83152 p x).
Proof. exact (eq_refl (term31 _83152 p x)). Qed.
Lemma lem3184395 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term43 _83152 p x) = (term37 _83152 p x).
Proof. exact (MK_COMB (@lem3184393 _83152 p x) (@lem3184394 _83152 p x)). Qed.
Lemma lem3184396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3184397 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term48 _83152 p x) = (term49 _83152 p x).
Proof. exact (MK_COMB (@lem3184396) (@lem3184395 _83152 p x)). Qed.
Lemma lem3184398 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term26 _83152 p x y) = (term17 _83152 p x y).
Proof. exact (eq_refl (term26 _83152 p x y)). Qed.
Lemma lem3184399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3184400 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term50 _83152 p x y) = (term51 _83152 p x y).
Proof. exact (MK_COMB (@lem3184399) (@lem3184398 _83152 p x y)). Qed.
Lemma lem3184401 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term31 _83152 p x) = (term31 _83152 p x).
Proof. exact (eq_refl (term31 _83152 p x)). Qed.
Lemma lem3184402 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) : (term52 _83152 y p x) = (term53 _83152 y p x).
Proof. exact (MK_COMB (@lem3184400 _83152 p x y) (@lem3184401 _83152 p x)). Qed.
Lemma lem3184403 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term54 _83152 p x) = (term55 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184402 _83152 y p x)). Qed.
Lemma lem3184404 {_83152 : Type'} : (@ex _83152) = (@ex _83152).
Proof. exact (eq_refl (@ex _83152)). Qed.
Lemma lem3184405 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term44 _83152 p x) = (term56 _83152 p x).
Proof. exact (MK_COMB (@lem3184404 _83152) (@lem3184403 _83152 p x)). Qed.
Lemma lem3184406 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term43 _83152 p x) = (term44 _83152 p x)) = ((term37 _83152 p x) = (term56 _83152 p x)).
Proof. exact (MK_COMB (@lem3184397 _83152 p x) (@lem3184405 _83152 p x)). Qed.
Lemma lem3184407 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term37 _83152 p x) = (term56 _83152 p x).
Proof. exact (EQ_MP (@lem3184406 _83152 p x) (@lem3184387 _83152 p x)). Qed.
Lemma lem3184408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3184409 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term38 _83152 p x) = (term57 _83152 p x).
Proof. exact (MK_COMB (@lem3184408) (@lem3184407 _83152 p x)). Qed.
Lemma lem3184410 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term35 _83152 p x) = (term35 _83152 p x).
Proof. exact (eq_refl (term35 _83152 p x)). Qed.
Lemma lem3184411 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term40 _83152 p x) = (term58 _83152 p x).
Proof. exact (MK_COMB (@lem3184409 _83152 p x) (@lem3184410 _83152 p x)). Qed.
Lemma lem3184413 {A : Type'} (P : A -> Prop) (Q : Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3184414 {_83152 : Type'} (P : _83152 -> Prop) (Q : Prop) : (term59 _83152 P Q) = (term60 _83152 P Q).
Proof. exact (@lem3184413 _83152 P Q). Qed.
Lemma lem3184415 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term61 _83152 p x) = (term62 _83152 p x).
Proof. exact (@lem3184414 _83152 (term55 _83152 p x) (term35 _83152 p x)). Qed.
Lemma lem3184416 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) : (term63 _83152 p x y) = (term53 _83152 y p x).
Proof. exact (eq_refl (term63 _83152 p x y)). Qed.
Lemma lem3184417 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term64 _83152 p x) = (term55 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184416 _83152 y p x)). Qed.
Lemma lem3184418 {_83152 : Type'} : (@ex _83152) = (@ex _83152).
Proof. exact (eq_refl (@ex _83152)). Qed.
Lemma lem3184419 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term65 _83152 p x) = (term56 _83152 p x).
Proof. exact (MK_COMB (@lem3184418 _83152) (@lem3184417 _83152 p x)). Qed.
Lemma lem3184420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3184421 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term66 _83152 p x) = (term57 _83152 p x).
Proof. exact (MK_COMB (@lem3184420) (@lem3184419 _83152 p x)). Qed.
Lemma lem3184422 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term35 _83152 p x) = (term35 _83152 p x).
Proof. exact (eq_refl (term35 _83152 p x)). Qed.
Lemma lem3184423 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term61 _83152 p x) = (term58 _83152 p x).
Proof. exact (MK_COMB (@lem3184421 _83152 p x) (@lem3184422 _83152 p x)). Qed.
Lemma lem3184424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3184425 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term67 _83152 p x) = (term68 _83152 p x).
Proof. exact (MK_COMB (@lem3184424) (@lem3184423 _83152 p x)). Qed.
Lemma lem3184426 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) : (term63 _83152 p x y) = (term53 _83152 y p x).
Proof. exact (eq_refl (term63 _83152 p x y)). Qed.
Lemma lem3184427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3184428 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) : (term69 _83152 p x y) = (term70 _83152 y p x).
Proof. exact (MK_COMB (@lem3184427) (@lem3184426 _83152 y p x)). Qed.
Lemma lem3184429 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term35 _83152 p x) = (term35 _83152 p x).
Proof. exact (eq_refl (term35 _83152 p x)). Qed.
Lemma lem3184430 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) : (term71 _83152 y p x) = (term72 _83152 y p x).
Proof. exact (MK_COMB (@lem3184428 _83152 y p x) (@lem3184429 _83152 p x)). Qed.
Lemma lem3184431 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term73 _83152 p x) = (term74 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184430 _83152 y p x)). Qed.
Lemma lem3184432 {_83152 : Type'} : (@ex _83152) = (@ex _83152).
Proof. exact (eq_refl (@ex _83152)). Qed.
Lemma lem3184433 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term62 _83152 p x) = (term75 _83152 p x).
Proof. exact (MK_COMB (@lem3184432 _83152) (@lem3184431 _83152 p x)). Qed.
Lemma lem3184434 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term61 _83152 p x) = (term62 _83152 p x)) = ((term58 _83152 p x) = (term75 _83152 p x)).
Proof. exact (MK_COMB (@lem3184425 _83152 p x) (@lem3184433 _83152 p x)). Qed.
Lemma lem3184435 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term58 _83152 p x) = (term75 _83152 p x).
Proof. exact (EQ_MP (@lem3184434 _83152 p x) (@lem3184415 _83152 p x)). Qed.
Lemma lem3184437 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term40 _83152 p x) = (term75 _83152 p x).
Proof. exact (TRANS (@lem3184411 _83152 p x) (@lem3184435 _83152 p x)). Qed.
Lemma lem3184438 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = (term75 _83152 p x).
Proof. exact (TRANS (@lem3184306 _83152 p x) (@lem3184437 _83152 p x)). Qed.
Lemma lem3184439 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : term75 _83152 p x.
Proof. exact (EQ_MP (@lem3184438 _83152 p x) (@lem3184268 _83152 p x h1)). Qed.
Lemma lem3184440 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term72 _83152 y p x) : term72 _83152 y p x.
Proof. exact (h1). Qed.
Lemma lem3184443 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3184458 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term21 _83152 p x y) = (term21 _83152 p x y).
Proof. exact (eq_refl (term21 _83152 p x y)). Qed.
Lemma lem3184459 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term29 _83152 p x) = (term29 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184458 _83152 p x y)). Qed.
Lemma lem3184460 {_83152 : Type'} : (@all _83152) = (@all _83152).
Proof. exact (eq_refl (@all _83152)). Qed.
Lemma lem3184461 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term30 _83152 p x) = (term30 _83152 p x).
Proof. exact (MK_COMB (@lem3184460 _83152) (@lem3184459 _83152 p x)). Qed.
Lemma lem3184462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3184463 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term33 _83152 p x) = (term33 _83152 p x).
Proof. exact (MK_COMB (@lem3184462) (@lem3184461 _83152 p x)). Qed.
Lemma lem3184464 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term35 _83152 p x) = (term35 _83152 p x).
Proof. exact (MK_COMB (@lem3184463 _83152 p x) (@lem3184443 _83152 p x)). Qed.
Lemma lem3184485 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) : (term70 _83152 y p x) = (term70 _83152 y p x).
Proof. exact (eq_refl (term70 _83152 y p x)). Qed.
Lemma lem3184486 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) : (term72 _83152 y p x) = (term72 _83152 y p x).
Proof. exact (MK_COMB (@lem3184485 _83152 y p x) (@lem3184464 _83152 p x)). Qed.
Lemma lem3184487 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term72 _83152 y p x) : term72 _83152 y p x.
Proof. exact (EQ_MP (@lem3184486 _83152 y p x) (@lem3184440 _83152 y p x h1)). Qed.
Lemma lem3184488 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : term53 _83152 y p x.
Proof. exact (h1). Qed.
Lemma lem3184489 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term35 _83152 p x.
Proof. exact (h1). Qed.
Lemma lem3184491 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : term17 _83152 p x y.
Proof. exact (proj1 (@lem3184488 _83152 y p x h1)). Qed.
Lemma lem3184495 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term30 _83152 p x.
Proof. exact (proj1 (@lem3184489 _83152 p x h1)). Qed.
Lemma lem3184515 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (y : _83152) : (term21 _83152 p x y) = (term21 _83152 p x y).
Proof. exact (eq_refl (term21 _83152 p x y)). Qed.
Lemma lem3184516 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term29 _83152 p x) = (term29 _83152 p x).
Proof. exact (fun_ext (fun y : _83152 => @lem3184515 _83152 p x y)). Qed.
Lemma lem3184517 {_83152 : Type'} : (@all _83152) = (@all _83152).
Proof. exact (eq_refl (@all _83152)). Qed.
Lemma lem3184519 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term30 _83152 p x) = (term30 _83152 p x).
Proof. exact (MK_COMB (@lem3184517 _83152) (@lem3184516 _83152 p x)). Qed.
Lemma lem3184520 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term30 _83152 p x.
Proof. exact (EQ_MP (@lem3184519 _83152 p x) (@lem3184495 _83152 p x h1)). Qed.
Lemma lem3184525 {_83152 : Type'} (_32730 : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term76 _83152 p x _32730.
Proof. exact (@lem3184520 _83152 p x h1 _32730). Qed.
Lemma lem3184526 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (_32730 : _83152) : (term76 _83152 p x _32730) = (term21 _83152 p x _32730).
Proof. exact (eq_refl (term76 _83152 p x _32730)). Qed.
Lemma lem3184529 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : term31 _83152 p x.
Proof. exact (proj2 (@lem3184488 _83152 y p x h1)). Qed.
Lemma lem3184533 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : x = y.
Proof. exact (proj2 (@lem3184491 _83152 y p x h1)). Qed.
Lemma lem3184539 {_83152 : Type'} (_32730 : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term21 _83152 p x _32730.
Proof. exact (EQ_MP (@lem3184526 _83152 p x _32730) (@lem3184525 _83152 _32730 p x h1)). Qed.
Lemma lem3184556 {_83152 : Type'} (p : _83152 -> Prop) : (term77 _83152 p) = (term77 _83152 p).
Proof. exact (eq_refl (term77 _83152 p)). Qed.
Lemma lem3184557 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : (term78 _83152 p x) = (term78 _83152 p y).
Proof. exact (MK_COMB (@lem3184556 _83152 p) (@lem3184533 _83152 y p x h1)). Qed.
Lemma lem3184558 {_83152 : Type'} (p : _83152 -> Prop) (y : _83152) : (term78 _83152 p y) = (term31 _83152 p y).
Proof. exact (eq_refl (term78 _83152 p y)). Qed.
Lemma lem3184559 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term79 _83152 p x) = (term79 _83152 p x).
Proof. exact (eq_refl (term79 _83152 p x)). Qed.
Lemma lem3184560 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) (y : _83152) : ((term78 _83152 p x) = (term78 _83152 p y)) = ((term78 _83152 p x) = (term31 _83152 p y)).
Proof. exact (MK_COMB (@lem3184559 _83152 p x) (@lem3184558 _83152 p y)). Qed.
Lemma lem3184561 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term78 _83152 p x) = (term31 _83152 p x).
Proof. exact (eq_refl (term78 _83152 p x)). Qed.
Lemma lem3184562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3184563 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term79 _83152 p x) = (term80 _83152 p x).
Proof. exact (MK_COMB (@lem3184562) (@lem3184561 _83152 p x)). Qed.
Lemma lem3184564 {_83152 : Type'} (p : _83152 -> Prop) (y : _83152) : (term31 _83152 p y) = (term31 _83152 p y).
Proof. exact (eq_refl (term31 _83152 p y)). Qed.
Lemma lem3184565 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) (y : _83152) : ((term78 _83152 p x) = (term31 _83152 p y)) = ((term31 _83152 p x) = (term31 _83152 p y)).
Proof. exact (MK_COMB (@lem3184563 _83152 p x) (@lem3184564 _83152 p y)). Qed.
Lemma lem3184566 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) (y : _83152) : ((term78 _83152 p x) = (term78 _83152 p y)) = ((term31 _83152 p x) = (term31 _83152 p y)).
Proof. exact (TRANS (@lem3184560 _83152 x p y) (@lem3184565 _83152 x p y)). Qed.
Lemma lem3184567 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : (term31 _83152 p x) = (term31 _83152 p y).
Proof. exact (EQ_MP (@lem3184566 _83152 x p y) (@lem3184557 _83152 y p x h1)). Qed.
Lemma lem3184568 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : term31 _83152 p y.
Proof. exact (EQ_MP (@lem3184567 _83152 y p x h1) (@lem3184529 _83152 y p x h1)). Qed.
Lemma lem3184584 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : p y.
Proof. exact (proj1 (@lem3184491 _83152 y p x h1)). Qed.
Lemma lem3184585 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : term81 _83152 p y.
Proof. exact (fun h0 : term31 _83152 p y => @lem3184584 _83152 y p x h1). Qed.
Lemma lem3184587 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184588 {_83152 : Type'} (p : _83152 -> Prop) (y : _83152) : (term81 _83152 p y) = (p y).
Proof. exact (@lem3184587 (p y)). Qed.
Lemma lem3184589 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : p y.
Proof. exact (EQ_MP (@lem3184588 _83152 p y) (@lem3184585 _83152 y p x h1)). Qed.
Lemma lem3184592 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3184594 {_83152 : Type'} (p : _83152 -> Prop) (y : _83152) : (term31 _83152 p y) = (term83 _83152 p y).
Proof. exact (@lem3184592 (p y)). Qed.
Lemma lem3184597 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : term83 _83152 p y.
Proof. exact (EQ_MP (@lem3184594 _83152 p y) (@lem3184568 _83152 y p x h1)). Qed.
Lemma lem3184600 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : False.
Proof. exact (@lem3184597 _83152 y p x h1 (@lem3184589 _83152 y p x h1)). Qed.
Lemma lem3184601 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : term84.
Proof. exact (fun h0 : ~ False => @lem3184600 _83152 y p x h1). Qed.
Lemma lem3184603 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184604 : term84 = False.
Proof. exact (@lem3184603 False). Qed.
Lemma lem3184621 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : p x.
Proof. exact (proj2 (@lem3184489 _83152 p x h1)). Qed.
Lemma lem3184622 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term81 _83152 p x.
Proof. exact (fun h0 : term31 _83152 p x => @lem3184621 _83152 p x h1). Qed.
Lemma lem3184624 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184625 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term81 _83152 p x) = (p x).
Proof. exact (@lem3184624 (p x)). Qed.
Lemma lem3184626 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : p x.
Proof. exact (EQ_MP (@lem3184625 _83152 p x) (@lem3184622 _83152 p x h1)). Qed.
Lemma lem3184628 {_83152 : Type'} (x : _83152) : x = x.
Proof. exact (@lem21386 _83152 x). Qed.
Lemma lem3184629 {_83152 : Type'} (x : _83152) : x = x.
Proof. exact (@lem3184628 _83152 x). Qed.
Lemma lem3184630 {_83152 : Type'} (x : _83152) : term85 _83152 x.
Proof. exact (fun h0 : term86 _83152 x => @lem3184629 _83152 x). Qed.
Lemma lem3184632 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184633 {_83152 : Type'} (x : _83152) : (term85 _83152 x) = (x = x).
Proof. exact (@lem3184632 (x = x)). Qed.
Lemma lem3184634 {_83152 : Type'} (x : _83152) : x = x.
Proof. exact (EQ_MP (@lem3184633 _83152 x) (@lem3184630 _83152 x)). Qed.
Lemma lem3184636 (a : Prop) (b : Prop) : (term87 a b) = (term88 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3184637 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (_32730 : _83152) : (term21 _83152 p x _32730) = (term20 _83152 p x _32730).
Proof. exact (@lem3184636 (p _32730) (x = _32730)). Qed.
Lemma lem3184639 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3184640 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (_32730 : _83152) : (term20 _83152 p x _32730) = (term89 _83152 p x _32730).
Proof. exact (@lem3184639 (term17 _83152 p x _32730)). Qed.
Lemma lem3184641 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (_32730 : _83152) : (term21 _83152 p x _32730) = (term89 _83152 p x _32730).
Proof. exact (TRANS (@lem3184637 _83152 p x _32730) (@lem3184640 _83152 p x _32730)). Qed.
Lemma lem3184643 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term90 _83152 p x.
Proof. exact (conj (@lem3184626 _83152 p x h1) (@lem3184634 _83152 x)). Qed.
Lemma lem3184645 {_83152 : Type'} (_32730 : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term89 _83152 p x _32730.
Proof. exact (EQ_MP (@lem3184641 _83152 p x _32730) (@lem3184539 _83152 _32730 p x h1)). Qed.
Lemma lem3184646 {_83152 : Type'} (_32730 : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term89 _83152 p x _32730.
Proof. exact (@lem3184645 _83152 _32730 p x h1). Qed.
Lemma lem3184647 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term91 _83152 p x.
Proof. exact (@lem3184646 _83152 x p x h1). Qed.
Lemma lem3184650 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : False.
Proof. exact (@lem3184647 _83152 p x h1 (@lem3184643 _83152 p x h1)). Qed.
Lemma lem3184651 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : term84.
Proof. exact (fun h0 : ~ False => @lem3184650 _83152 p x h1). Qed.
Lemma lem3184653 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184654 : term84 = False.
Proof. exact (@lem3184653 False). Qed.
Lemma lem3184655 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term35 _83152 p x) : False.
Proof. exact (EQ_MP (@lem3184654) (@lem3184651 _83152 p x h1)). Qed.
Lemma lem3184656 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term53 _83152 y p x) : False.
Proof. exact (EQ_MP (@lem3184604) (@lem3184601 _83152 y p x h1)). Qed.
Lemma lem3184657 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term72 _83152 y p x) : False.
Proof. exact (or_elim (@lem3184487 _83152 y p x h1) (fun h0 : term53 _83152 y p x => @lem3184656 _83152 y p x h0) (fun h0 : term35 _83152 p x => @lem3184655 _83152 p x h0)). Qed.
Lemma lem3184658 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term72 _83152 y p x) : (term72 _83152 y p x) = False.
Proof. exact (prop_ext (fun h2 : term72 _83152 y p x => @lem3184657 _83152 y p x h1) (fun h2 : False => @lem3184487 _83152 y p x h1)). Qed.
Lemma lem3184659 {_83152 : Type'} (y : _83152) (p : _83152 -> Prop) (x : _83152) (h1 : term72 _83152 y p x) : False.
Proof. exact (EQ_MP (@lem3184658 _83152 y p x h1) (@lem3184487 _83152 y p x h1)). Qed.
Lemma lem3184660 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : False.
Proof. exact (ex_elim (@lem3184439 _83152 p x h1) (fun y : _83152 => fun h0 : term74 _83152 p x y => @lem3184659 _83152 y p x h0)). Qed.
Lemma lem3184661 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : (term3 _83152 p x) = False.
Proof. exact (prop_ext (fun h2 : term3 _83152 p x => @lem3184660 _83152 p x h1) (fun h2 : False => @lem3184268 _83152 p x h1)). Qed.
Lemma lem3184662 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : False.
Proof. exact (EQ_MP (@lem3184661 _83152 p x h1) (@lem3184268 _83152 p x h1)). Qed.
Lemma lem3184663 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term2 _83152 p x.
Proof. exact (fun h0 : term3 _83152 p x => @lem3184662 _83152 p x h0). Qed.
Lemma lem3184664 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term1 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem3184267 _83152 p x) (@lem3184663 _83152 p x)). Qed.
Lemma lem3184669 {_83152 : Type'} (x : _83152) : term12 _83152 x.
Proof. exact (fun p : _83152 -> Prop => @lem3184664 _83152 p x). Qed.
Lemma lem3184674 {_83152 : Type'} : term16 _83152.
Proof. exact (fun x : _83152 => @lem3184669 _83152 x). Qed.
Lemma lem3184675 {_83152 : Type'} : term15 _83152.
Proof. exact (EQ_MP (@lem3184263 _83152) (@lem3184674 _83152)). Qed.
Lemma lem3184676 {_83152 : Type'} (x : _83152) : term92 _83152 x.
Proof. exact (@lem3184675 _83152 x). Qed.
Lemma lem3184677 {_83152 : Type'} (x : _83152) : (term92 _83152 x) = (term11 _83152 x).
Proof. exact (eq_refl (term92 _83152 x)). Qed.
Lemma lem3184678 {_83152 : Type'} (x : _83152) : term11 _83152 x.
Proof. exact (EQ_MP (@lem3184677 _83152 x) (@lem3184676 _83152 x)). Qed.
Lemma lem3184679 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) : term93 _83152 x p.
Proof. exact (@lem3184678 _83152 x p). Qed.
Lemma lem3184680 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term93 _83152 x p) = (term2 _83152 p x).
Proof. exact (eq_refl (term93 _83152 x p)). Qed.
Lemma lem3184681 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term2 _83152 p x.
Proof. exact (EQ_MP (@lem3184680 _83152 p x) (@lem3184679 _83152 x p)). Qed.
Lemma lem3184683 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term2 _83152 p x.
Proof. exact (@lem3184158 _83152 p x (@lem3184681 _83152 p x)). Qed.
Lemma lem3184684 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : False.
Proof. exact (@lem3184683 _83152 p x (@lem3184142 _83152 p x h1)). Qed.
Lemma lem3184685 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : (term3 _83152 p x) = False.
Proof. exact (prop_ext (fun h2 : term3 _83152 p x => @lem3184684 _83152 p x h1) (fun h2 : False => @lem3184142 _83152 p x h1)). Qed.
Lemma lem3184686 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) (h1 : term3 _83152 p x) : False.
Proof. exact (EQ_MP (@lem3184685 _83152 p x h1) (@lem3184142 _83152 p x h1)). Qed.
Lemma lem3184687 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term2 _83152 p x.
Proof. exact (fun h0 : term3 _83152 p x => @lem3184686 _83152 p x h0). Qed.
Lemma lem3184688 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term1 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem3184141 _83152 p x) (@lem3184687 _83152 p x)). Qed.
Lemma lem3184689 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term94 _83152 x p) = (p x).
Proof. exact (EQ_MP (@lem3183586 _83152 p x) (@lem3184688 _83152 p x)). Qed.
