Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_DELETE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_DELETE_spec.
Require Import INSERT_DELETE_spec.
Require Import IN_DELETE_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem5811947 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5811948 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (@lem5811947 (term1 A B)). Qed.
Lemma lem5811949 {A B : Type'} : (term2 A B) = (term1 A B).
Proof. exact (SYM (@lem5811948 A B)). Qed.
Lemma lem5811950 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem5811951 {_120477 _120521 B : Type'} : term4 _120477 _120521 B.
Proof. exact (@lem5753565 _120477 B _120521). Qed.
Lemma lem5811953 {_120521 A B : Type'} : term5 _120521 A B.
Proof. exact (@lem5753565 A B _120521). Qed.
Lemma lem5811954 {_120477 _120519 A : Type'} : term6 _120477 _120519 A.
Proof. exact (@lem5753565 _120477 _120519 A). Qed.
Lemma lem5811955 {_120477 A B : Type'} : term4 _120477 A B.
Proof. exact (@lem5753565 _120477 B A). Qed.
Lemma lem5811957 {A : Type'} : term7 A.
Proof. exact (@lem3610594 A). Qed.
Lemma lem5811958 {_120521 : Type'} : term7 _120521.
Proof. exact (@lem3610594 _120521). Qed.
Lemma lem5811960 {A : Type'} : term8 A.
Proof. exact (@lem3205803 A). Qed.
Lemma lem5811961 {_120521 : Type'} : term8 _120521.
Proof. exact (@lem3205803 _120521). Qed.
Lemma lem5811964 {B : Type'} : term8 B.
Proof. exact (@lem3205803 B). Qed.
Lemma lem5811965 {_120519 : Type'} : term8 _120519.
Proof. exact (@lem3205803 _120519). Qed.
Lemma lem5811966 {A : Type'} : term9 A.
Proof. exact (@lem3319650 A). Qed.
Lemma lem5811967 {_120521 : Type'} : term9 _120521.
Proof. exact (@lem3319650 _120521). Qed.
Lemma lem5811968 {B : Type'} : term9 B.
Proof. exact (@lem3319650 B). Qed.
Lemma lem5811969 {_120519 : Type'} : term9 _120519.
Proof. exact (@lem3319650 _120519). Qed.
Lemma lem5811978 {_120477 _120519 _120521 A B : Type'} (h1 : term10 _120477 _120519 _120521 A B) : term10 _120477 _120519 _120521 A B.
Proof. exact (h1). Qed.
Lemma lem5811979 {_120477 _120519 _120521 A B : Type'} : term11 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term10 _120477 _120519 _120521 A B => @lem5811978 _120477 _120519 _120521 A B h0). Qed.
Lemma lem5811980 {_120477 _120519 _120521 A B : Type'} (h1 : term11 _120477 _120519 _120521 A B) : term11 _120477 _120519 _120521 A B.
Proof. exact (h1). Qed.
Lemma lem5811981 {_120477 _120519 _120521 A B : Type'} (h1 : term10 _120477 _120519 _120521 A B) : term10 _120477 _120519 _120521 A B.
Proof. exact (h1). Qed.
Lemma lem5811982 {_120477 _120519 _120521 A B : Type'} (h1 : term10 _120477 _120519 _120521 A B) (h2 : term11 _120477 _120519 _120521 A B) : term10 _120477 _120519 _120521 A B.
Proof. exact (@lem5811980 _120477 _120519 _120521 A B h2 (@lem5811981 _120477 _120519 _120521 A B h1)). Qed.
Lemma lem5811983 {_120477 _120519 _120521 A B : Type'} (h1 : term10 _120477 _120519 _120521 A B) : term12 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term11 _120477 _120519 _120521 A B => @lem5811982 _120477 _120519 _120521 A B h1 h0). Qed.
Lemma lem5811984 {_120477 _120519 _120521 A B : Type'} (h1 : term11 _120477 _120519 _120521 A B) : term11 _120477 _120519 _120521 A B.
Proof. exact (h1). Qed.
Lemma lem5811985 {_120477 _120519 _120521 A B : Type'} (h1 : term10 _120477 _120519 _120521 A B) (h2 : term11 _120477 _120519 _120521 A B) : term10 _120477 _120519 _120521 A B.
Proof. exact (@lem5811983 _120477 _120519 _120521 A B h1 (@lem5811984 _120477 _120519 _120521 A B h2)). Qed.
Lemma lem5811986 {_120477 _120519 _120521 A B : Type'} (h1 : term11 _120477 _120519 _120521 A B) : term11 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term10 _120477 _120519 _120521 A B => @lem5811985 _120477 _120519 _120521 A B h0 h1). Qed.
Lemma lem5811987 {_120477 _120519 _120521 A B : Type'} : term13 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term11 _120477 _120519 _120521 A B => @lem5811986 _120477 _120519 _120521 A B h0). Qed.
Lemma lem5811990 {_120477 _120519 _120521 A B : Type'} : term11 _120477 _120519 _120521 A B.
Proof. exact (@lem5811987 _120477 _120519 _120521 A B (@lem5811979 _120477 _120519 _120521 A B)). Qed.
Lemma lem5811991 {_120477 _120519 _120521 A B : Type'} : term11 _120477 _120519 _120521 A B.
Proof. exact (@lem5811990 _120477 _120519 _120521 A B). Qed.
Lemma lem5812233 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5812234 {_120521 A B : Type'} : (term14 _120521 A B) = (term15 _120521 A B).
Proof. exact (@lem5812233 (term5 _120521 A B)). Qed.
Lemma lem5812261 {_120477 A B : Type'} : (term16 _120477 A B) = (term16 _120477 A B).
Proof. exact (eq_refl (term16 _120477 A B)). Qed.
Lemma lem5812262 {_120477 _120521 A B : Type'} : (term17 _120477 _120521 A B) = (term18 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5812261 _120477 A B) (@lem5812234 _120521 A B)). Qed.
Lemma lem5812265 {_120477 _120521 B : Type'} : (term16 _120477 _120521 B) = (term16 _120477 _120521 B).
Proof. exact (eq_refl (term16 _120477 _120521 B)). Qed.
Lemma lem5812266 {_120477 _120521 A B : Type'} : (term19 _120477 _120521 A B) = (term20 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5812265 _120477 _120521 B) (@lem5812262 _120477 _120521 A B)). Qed.
Lemma lem5812269 {_120477 _120519 A : Type'} : (term21 _120477 _120519 A) = (term21 _120477 _120519 A).
Proof. exact (eq_refl (term21 _120477 _120519 A)). Qed.
Lemma lem5812270 {_120477 _120519 _120521 A B : Type'} : (term22 _120477 _120519 _120521 A B) = (term23 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812269 _120477 _120519 A) (@lem5812266 _120477 _120521 A B)). Qed.
Lemma lem5812273 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (eq_refl (term24 A)). Qed.
Lemma lem5812274 {_120477 _120519 _120521 A B : Type'} : (term25 _120477 _120519 _120521 A B) = (term26 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812273 A) (@lem5812270 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812277 {_120521 : Type'} : (term24 _120521) = (term24 _120521).
Proof. exact (eq_refl (term24 _120521)). Qed.
Lemma lem5812278 {_120477 _120519 _120521 A B : Type'} : (term27 _120477 _120519 _120521 A B) = (term28 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812277 _120521) (@lem5812274 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812281 {B : Type'} : (term29 B) = (term29 B).
Proof. exact (eq_refl (term29 B)). Qed.
Lemma lem5812282 {_120477 _120519 _120521 A B : Type'} : (term30 _120477 _120519 _120521 A B) = (term31 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812281 B) (@lem5812278 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812285 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (eq_refl (term29 A)). Qed.
Lemma lem5812286 {_120477 _120519 _120521 A B : Type'} : (term32 _120477 _120519 _120521 A B) = (term33 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812285 A) (@lem5812282 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812289 {_120521 : Type'} : (term29 _120521) = (term29 _120521).
Proof. exact (eq_refl (term29 _120521)). Qed.
Lemma lem5812290 {_120477 _120519 _120521 A B : Type'} : (term34 _120477 _120519 _120521 A B) = (term35 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812289 _120521) (@lem5812286 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812293 {_120519 : Type'} : (term29 _120519) = (term29 _120519).
Proof. exact (eq_refl (term29 _120519)). Qed.
Lemma lem5812294 {_120477 _120519 _120521 A B : Type'} : (term36 _120477 _120519 _120521 A B) = (term37 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812293 _120519) (@lem5812290 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812297 {B : Type'} : (term38 B) = (term38 B).
Proof. exact (eq_refl (term38 B)). Qed.
Lemma lem5812298 {_120477 _120519 _120521 A B : Type'} : (term39 _120477 _120519 _120521 A B) = (term40 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812297 B) (@lem5812294 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812301 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (eq_refl (term38 A)). Qed.
Lemma lem5812302 {_120477 _120519 _120521 A B : Type'} : (term41 _120477 _120519 _120521 A B) = (term42 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812301 A) (@lem5812298 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812305 {_120521 : Type'} : (term38 _120521) = (term38 _120521).
Proof. exact (eq_refl (term38 _120521)). Qed.
Lemma lem5812306 {_120477 _120519 _120521 A B : Type'} : (term43 _120477 _120519 _120521 A B) = (term44 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812305 _120521) (@lem5812302 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812309 {_120519 : Type'} : (term38 _120519) = (term38 _120519).
Proof. exact (eq_refl (term38 _120519)). Qed.
Lemma lem5812310 {_120477 _120519 _120521 A B : Type'} : (term45 _120477 _120519 _120521 A B) = (term46 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812309 _120519) (@lem5812306 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812313 {A B : Type'} : (term47 A B) = (term47 A B).
Proof. exact (eq_refl (term47 A B)). Qed.
Lemma lem5812320 {_120477 _120519 _120521 A B : Type'} : (term10 _120477 _120519 _120521 A B) = (term48 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812313 A B) (@lem5812310 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812324 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (@IN _120521 x s) = False.
Proof. exact (h1). Qed.
Lemma lem5812325 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5812326 {_120521 B : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term49 _120521 B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem5812325 B) (@lem5812324 _120521 x s h1)). Qed.
Lemma lem5812327 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (@iterate B _120521 op s f).
Proof. exact (eq_refl (@iterate B _120521 op s f)). Qed.
Lemma lem5812328 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term50 _120521 B x op s f) = (term51 _120521 B op s f).
Proof. exact (MK_COMB (@lem5812326 _120521 B x s h1) (@lem5812327 _120521 B op s f)). Qed.
Lemma lem5812329 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term52 _120521 B x op s f) = (term52 _120521 B x op s f).
Proof. exact (eq_refl (term52 _120521 B x op s f)). Qed.
Lemma lem5812330 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term53 _120521 B x op s f) = (term54 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5812328 _120521 B op f x s h1) (@lem5812329 _120521 B x op s f)). Qed.
Lemma lem5812332 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5812333 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5812332 B t1 t2). Qed.
Lemma lem5812334 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term54 _120521 B x op s f) = (term52 _120521 B x op s f).
Proof. exact (@lem5812333 B (@iterate B _120521 op s f) (term52 _120521 B x op s f)). Qed.
Lemma lem5812335 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term53 _120521 B x op s f) = (term52 _120521 B x op s f).
Proof. exact (TRANS (@lem5812330 _120521 B op f x s h1) (@lem5812334 _120521 B x op s f)). Qed.
Lemma lem5812336 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term55 _120521 B op x s f) = (term55 _120521 B op x s f).
Proof. exact (eq_refl (term55 _120521 B op x s f)). Qed.
Lemma lem5812337 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : ((term56 _120521 B op x s f) = (term53 _120521 B x op s f)) = ((term56 _120521 B op x s f) = (term52 _120521 B x op s f)).
Proof. exact (MK_COMB (@lem5812336 _120521 B op x s f) (@lem5812335 _120521 B op f x s h1)). Qed.
Lemma lem5812340 {_120521 : Type'} (s : _120521 -> Prop) : (term57 _120521 s) = (term57 _120521 s).
Proof. exact (eq_refl (term57 _120521 s)). Qed.
Lemma lem5812341 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term58 _120521 B x op s f) = (term59 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5812340 _120521 s) (@lem5812337 _120521 B op f x s h1)). Qed.
Lemma lem5812344 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term60 _120521 B x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = False => @lem5812341 _120521 B op f x s h0). Qed.
Lemma lem5812346 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (@IN _120521 x s) = True.
Proof. exact (h1). Qed.
Lemma lem5812347 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5812348 {_120521 B : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term49 _120521 B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem5812347 B) (@lem5812346 _120521 x s h1)). Qed.
Lemma lem5812349 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (@iterate B _120521 op s f).
Proof. exact (eq_refl (@iterate B _120521 op s f)). Qed.
Lemma lem5812350 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term50 _120521 B x op s f) = (term61 _120521 B op s f).
Proof. exact (MK_COMB (@lem5812348 _120521 B x s h1) (@lem5812349 _120521 B op s f)). Qed.
Lemma lem5812351 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term52 _120521 B x op s f) = (term52 _120521 B x op s f).
Proof. exact (eq_refl (term52 _120521 B x op s f)). Qed.
Lemma lem5812352 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term53 _120521 B x op s f) = (term62 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5812350 _120521 B op f x s h1) (@lem5812351 _120521 B x op s f)). Qed.
Lemma lem5812354 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5812355 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5812354 B t2 t1). Qed.
Lemma lem5812356 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term62 _120521 B x op s f) = (@iterate B _120521 op s f).
Proof. exact (@lem5812355 B (term52 _120521 B x op s f) (@iterate B _120521 op s f)). Qed.
Lemma lem5812357 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term53 _120521 B x op s f) = (@iterate B _120521 op s f).
Proof. exact (TRANS (@lem5812352 _120521 B op f x s h1) (@lem5812356 _120521 B x op s f)). Qed.
Lemma lem5812358 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term55 _120521 B op x s f) = (term55 _120521 B op x s f).
Proof. exact (eq_refl (term55 _120521 B op x s f)). Qed.
Lemma lem5812359 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : ((term56 _120521 B op x s f) = (term53 _120521 B x op s f)) = ((term56 _120521 B op x s f) = (@iterate B _120521 op s f)).
Proof. exact (MK_COMB (@lem5812358 _120521 B op x s f) (@lem5812357 _120521 B op f x s h1)). Qed.
Lemma lem5812362 {_120521 : Type'} (s : _120521 -> Prop) : (term57 _120521 s) = (term57 _120521 s).
Proof. exact (eq_refl (term57 _120521 s)). Qed.
Lemma lem5812363 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term58 _120521 B x op s f) = (term63 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5812362 _120521 s) (@lem5812359 _120521 B op f x s h1)). Qed.
Lemma lem5812366 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term64 _120521 B x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = True => @lem5812363 _120521 B op f x s h0). Qed.
Lemma lem5812367 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term65 _120521 B x op s f.
Proof. exact (conj (@lem5812344 _120521 B x op s f) (@lem5812366 _120521 B x op s f)). Qed.
Lemma lem5812369 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term66 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5812370 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term67 _120521 B x op s f.
Proof. exact (@lem5812369 (term58 _120521 B x op s f) (term63 _120521 B x op s f) (@IN _120521 x s) (term59 _120521 B x op s f)). Qed.
Lemma lem5812411 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term58 _120521 B x op s f) = (term68 _120521 B x op s f).
Proof. exact (@lem5812370 _120521 B x op s f (@lem5812367 _120521 B x op s f)). Qed.
Lemma lem5812412 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term69 _120521 B x op f) = (term70 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5812411 _120521 B x op s f)). Qed.
Lemma lem5812413 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5812414 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term71 _120521 B x op f) = (term72 _120521 B x op f).
Proof. exact (MK_COMB (@lem5812413 _120521) (@lem5812412 _120521 B x op f)). Qed.
Lemma lem5812415 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term73 _120521 B op f) = (term74 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5812414 _120521 B x op f)). Qed.
Lemma lem5812416 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5812417 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term75 _120521 B op f) = (term76 _120521 B op f).
Proof. exact (MK_COMB (@lem5812416 _120521) (@lem5812415 _120521 B op f)). Qed.
Lemma lem5812418 {_120521 B : Type'} (op : type1400 B) : (term77 _120521 B op) = (term78 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5812417 _120521 B op f)). Qed.
Lemma lem5812419 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5812420 {_120521 B : Type'} (op : type1400 B) : (term79 _120521 B op) = (term80 _120521 B op).
Proof. exact (MK_COMB (@lem5812419 _120521 B) (@lem5812418 _120521 B op)). Qed.
Lemma lem5812421 {A B : Type'} (f : A -> B) (op : type1400 B) : ((@iterate B A op (@EMPTY A) f) = (@neutral B op)) = ((@iterate B A op (@EMPTY A) f) = (@neutral B op)).
Proof. exact (eq_refl ((@iterate B A op (@EMPTY A) f) = (@neutral B op))). Qed.
Lemma lem5812422 {A B : Type'} (op : type1400 B) : (term81 A B op) = (term81 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5812421 A B f op)). Qed.
Lemma lem5812423 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5812424 {A B : Type'} (op : type1400 B) : (term82 A B op) = (term82 A B op).
Proof. exact (MK_COMB (@lem5812423 A B) (@lem5812422 A B op)). Qed.
Lemma lem5812425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5812426 {A B : Type'} (op : type1400 B) : (term83 A B op) = (term83 A B op).
Proof. exact (MK_COMB (@lem5812425) (@lem5812424 A B op)). Qed.
Lemma lem5812427 {_120521 A B : Type'} (op : type1400 B) : (term84 _120521 A B op) = (term85 _120521 A B op).
Proof. exact (MK_COMB (@lem5812426 A B op) (@lem5812420 _120521 B op)). Qed.
Lemma lem5812430 {B : Type'} (op : type1400 B) : (term86 B op) = (term86 B op).
Proof. exact (eq_refl (term86 B op)). Qed.
Lemma lem5812431 {_120521 A B : Type'} (op : type1400 B) : (term87 _120521 A B op) = (term88 _120521 A B op).
Proof. exact (MK_COMB (@lem5812430 B op) (@lem5812427 _120521 A B op)). Qed.
Lemma lem5812432 {_120521 A B : Type'} : (term89 _120521 A B) = (term90 _120521 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5812431 _120521 A B op)). Qed.
Lemma lem5812433 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5812434 {_120521 A B : Type'} : (term5 _120521 A B) = (term91 _120521 A B).
Proof. exact (MK_COMB (@lem5812433 B) (@lem5812432 _120521 A B)). Qed.
Lemma lem5812435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5812436 {_120521 A B : Type'} : (term15 _120521 A B) = (term92 _120521 A B).
Proof. exact (MK_COMB (@lem5812435) (@lem5812434 _120521 A B)). Qed.
Lemma lem5812440 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem5812441 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5812442 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term49 A B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem5812441 B) (@lem5812440 A x s h1)). Qed.
Lemma lem5812443 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (@iterate B A op s f).
Proof. exact (eq_refl (@iterate B A op s f)). Qed.
Lemma lem5812444 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term50 A B x op s f) = (term51 A B op s f).
Proof. exact (MK_COMB (@lem5812442 A B x s h1) (@lem5812443 A B op s f)). Qed.
Lemma lem5812445 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term52 A B x op s f) = (term52 A B x op s f).
Proof. exact (eq_refl (term52 A B x op s f)). Qed.
Lemma lem5812446 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term53 A B x op s f) = (term54 A B x op s f).
Proof. exact (MK_COMB (@lem5812444 A B op f x s h1) (@lem5812445 A B x op s f)). Qed.
Lemma lem5812448 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5812449 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5812448 B t1 t2). Qed.
Lemma lem5812450 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term54 A B x op s f) = (term52 A B x op s f).
Proof. exact (@lem5812449 B (@iterate B A op s f) (term52 A B x op s f)). Qed.
Lemma lem5812451 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term53 A B x op s f) = (term52 A B x op s f).
Proof. exact (TRANS (@lem5812446 A B op f x s h1) (@lem5812450 A B x op s f)). Qed.
Lemma lem5812452 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term55 A B op x s f) = (term55 A B op x s f).
Proof. exact (eq_refl (term55 A B op x s f)). Qed.
Lemma lem5812453 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term56 A B op x s f) = (term53 A B x op s f)) = ((term56 A B op x s f) = (term52 A B x op s f)).
Proof. exact (MK_COMB (@lem5812452 A B op x s f) (@lem5812451 A B op f x s h1)). Qed.
Lemma lem5812456 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem5812457 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term58 A B x op s f) = (term59 A B x op s f).
Proof. exact (MK_COMB (@lem5812456 A s) (@lem5812453 A B op f x s h1)). Qed.
Lemma lem5812460 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term60 A B x op s f.
Proof. exact (fun h0 : (@IN A x s) = False => @lem5812457 A B op f x s h0). Qed.
Lemma lem5812462 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem5812463 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5812464 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term49 A B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem5812463 B) (@lem5812462 A x s h1)). Qed.
Lemma lem5812465 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (@iterate B A op s f).
Proof. exact (eq_refl (@iterate B A op s f)). Qed.
Lemma lem5812466 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term50 A B x op s f) = (term61 A B op s f).
Proof. exact (MK_COMB (@lem5812464 A B x s h1) (@lem5812465 A B op s f)). Qed.
Lemma lem5812467 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term52 A B x op s f) = (term52 A B x op s f).
Proof. exact (eq_refl (term52 A B x op s f)). Qed.
Lemma lem5812468 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term53 A B x op s f) = (term62 A B x op s f).
Proof. exact (MK_COMB (@lem5812466 A B op f x s h1) (@lem5812467 A B x op s f)). Qed.
Lemma lem5812470 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5812471 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5812470 B t2 t1). Qed.
Lemma lem5812472 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term62 A B x op s f) = (@iterate B A op s f).
Proof. exact (@lem5812471 B (term52 A B x op s f) (@iterate B A op s f)). Qed.
Lemma lem5812473 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term53 A B x op s f) = (@iterate B A op s f).
Proof. exact (TRANS (@lem5812468 A B op f x s h1) (@lem5812472 A B x op s f)). Qed.
Lemma lem5812474 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term55 A B op x s f) = (term55 A B op x s f).
Proof. exact (eq_refl (term55 A B op x s f)). Qed.
Lemma lem5812475 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term56 A B op x s f) = (term53 A B x op s f)) = ((term56 A B op x s f) = (@iterate B A op s f)).
Proof. exact (MK_COMB (@lem5812474 A B op x s f) (@lem5812473 A B op f x s h1)). Qed.
Lemma lem5812478 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem5812479 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term58 A B x op s f) = (term63 A B x op s f).
Proof. exact (MK_COMB (@lem5812478 A s) (@lem5812475 A B op f x s h1)). Qed.
Lemma lem5812482 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term64 A B x op s f.
Proof. exact (fun h0 : (@IN A x s) = True => @lem5812479 A B op f x s h0). Qed.
Lemma lem5812483 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term65 A B x op s f.
Proof. exact (conj (@lem5812460 A B x op s f) (@lem5812482 A B x op s f)). Qed.
Lemma lem5812485 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term66 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5812486 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term67 A B x op s f.
Proof. exact (@lem5812485 (term58 A B x op s f) (term63 A B x op s f) (@IN A x s) (term59 A B x op s f)). Qed.
Lemma lem5812527 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term58 A B x op s f) = (term68 A B x op s f).
Proof. exact (@lem5812486 A B x op s f (@lem5812483 A B x op s f)). Qed.
Lemma lem5812528 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term69 A B x op f) = (term70 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5812527 A B x op s f)). Qed.
Lemma lem5812529 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5812530 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term71 A B x op f) = (term72 A B x op f).
Proof. exact (MK_COMB (@lem5812529 A) (@lem5812528 A B x op f)). Qed.
Lemma lem5812531 {A B : Type'} (op : type1400 B) (f : A -> B) : (term73 A B op f) = (term74 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5812530 A B x op f)). Qed.
Lemma lem5812532 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5812533 {A B : Type'} (op : type1400 B) (f : A -> B) : (term75 A B op f) = (term76 A B op f).
Proof. exact (MK_COMB (@lem5812532 A) (@lem5812531 A B op f)). Qed.
Lemma lem5812534 {A B : Type'} (op : type1400 B) : (term77 A B op) = (term78 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5812533 A B op f)). Qed.
Lemma lem5812535 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5812536 {A B : Type'} (op : type1400 B) : (term79 A B op) = (term80 A B op).
Proof. exact (MK_COMB (@lem5812535 A B) (@lem5812534 A B op)). Qed.
Lemma lem5812537 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)) = ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)).
Proof. exact (eq_refl ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op))). Qed.
Lemma lem5812538 {_120477 B : Type'} (op : type1400 B) : (term81 _120477 B op) = (term81 _120477 B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5812537 _120477 B f op)). Qed.
Lemma lem5812539 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5812540 {_120477 B : Type'} (op : type1400 B) : (term82 _120477 B op) = (term82 _120477 B op).
Proof. exact (MK_COMB (@lem5812539 _120477 B) (@lem5812538 _120477 B op)). Qed.
Lemma lem5812541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5812542 {_120477 B : Type'} (op : type1400 B) : (term83 _120477 B op) = (term83 _120477 B op).
Proof. exact (MK_COMB (@lem5812541) (@lem5812540 _120477 B op)). Qed.
Lemma lem5812543 {_120477 A B : Type'} (op : type1400 B) : (term93 _120477 A B op) = (term94 _120477 A B op).
Proof. exact (MK_COMB (@lem5812542 _120477 B op) (@lem5812536 A B op)). Qed.
Lemma lem5812546 {B : Type'} (op : type1400 B) : (term86 B op) = (term86 B op).
Proof. exact (eq_refl (term86 B op)). Qed.
Lemma lem5812547 {_120477 A B : Type'} (op : type1400 B) : (term95 _120477 A B op) = (term96 _120477 A B op).
Proof. exact (MK_COMB (@lem5812546 B op) (@lem5812543 _120477 A B op)). Qed.
Lemma lem5812548 {_120477 A B : Type'} : (term97 _120477 A B) = (term98 _120477 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5812547 _120477 A B op)). Qed.
Lemma lem5812549 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5812550 {_120477 A B : Type'} : (term4 _120477 A B) = (term99 _120477 A B).
Proof. exact (MK_COMB (@lem5812549 B) (@lem5812548 _120477 A B)). Qed.
Lemma lem5812551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812552 {_120477 A B : Type'} : (term16 _120477 A B) = (term100 _120477 A B).
Proof. exact (MK_COMB (@lem5812551) (@lem5812550 _120477 A B)). Qed.
Lemma lem5812553 {_120477 _120521 A B : Type'} : (term18 _120477 _120521 A B) = (term101 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5812552 _120477 A B) (@lem5812436 _120521 A B)). Qed.
Lemma lem5812557 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (@IN _120521 x s) = False.
Proof. exact (h1). Qed.
Lemma lem5812558 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5812559 {_120521 B : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term49 _120521 B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem5812558 B) (@lem5812557 _120521 x s h1)). Qed.
Lemma lem5812560 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (@iterate B _120521 op s f).
Proof. exact (eq_refl (@iterate B _120521 op s f)). Qed.
Lemma lem5812561 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term50 _120521 B x op s f) = (term51 _120521 B op s f).
Proof. exact (MK_COMB (@lem5812559 _120521 B x s h1) (@lem5812560 _120521 B op s f)). Qed.
Lemma lem5812562 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term52 _120521 B x op s f) = (term52 _120521 B x op s f).
Proof. exact (eq_refl (term52 _120521 B x op s f)). Qed.
Lemma lem5812563 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term53 _120521 B x op s f) = (term54 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5812561 _120521 B op f x s h1) (@lem5812562 _120521 B x op s f)). Qed.
Lemma lem5812565 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5812566 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5812565 B t1 t2). Qed.
Lemma lem5812567 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term54 _120521 B x op s f) = (term52 _120521 B x op s f).
Proof. exact (@lem5812566 B (@iterate B _120521 op s f) (term52 _120521 B x op s f)). Qed.
Lemma lem5812568 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term53 _120521 B x op s f) = (term52 _120521 B x op s f).
Proof. exact (TRANS (@lem5812563 _120521 B op f x s h1) (@lem5812567 _120521 B x op s f)). Qed.
Lemma lem5812569 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term55 _120521 B op x s f) = (term55 _120521 B op x s f).
Proof. exact (eq_refl (term55 _120521 B op x s f)). Qed.
Lemma lem5812570 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : ((term56 _120521 B op x s f) = (term53 _120521 B x op s f)) = ((term56 _120521 B op x s f) = (term52 _120521 B x op s f)).
Proof. exact (MK_COMB (@lem5812569 _120521 B op x s f) (@lem5812568 _120521 B op f x s h1)). Qed.
Lemma lem5812573 {_120521 : Type'} (s : _120521 -> Prop) : (term57 _120521 s) = (term57 _120521 s).
Proof. exact (eq_refl (term57 _120521 s)). Qed.
Lemma lem5812574 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = False) : (term58 _120521 B x op s f) = (term59 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5812573 _120521 s) (@lem5812570 _120521 B op f x s h1)). Qed.
Lemma lem5812577 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term60 _120521 B x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = False => @lem5812574 _120521 B op f x s h0). Qed.
Lemma lem5812579 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (@IN _120521 x s) = True.
Proof. exact (h1). Qed.
Lemma lem5812580 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5812581 {_120521 B : Type'} (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term49 _120521 B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem5812580 B) (@lem5812579 _120521 x s h1)). Qed.
Lemma lem5812582 {_120521 B : Type'} (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (@iterate B _120521 op s f) = (@iterate B _120521 op s f).
Proof. exact (eq_refl (@iterate B _120521 op s f)). Qed.
Lemma lem5812583 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term50 _120521 B x op s f) = (term61 _120521 B op s f).
Proof. exact (MK_COMB (@lem5812581 _120521 B x s h1) (@lem5812582 _120521 B op s f)). Qed.
Lemma lem5812584 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term52 _120521 B x op s f) = (term52 _120521 B x op s f).
Proof. exact (eq_refl (term52 _120521 B x op s f)). Qed.
Lemma lem5812585 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term53 _120521 B x op s f) = (term62 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5812583 _120521 B op f x s h1) (@lem5812584 _120521 B x op s f)). Qed.
Lemma lem5812587 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5812588 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5812587 B t2 t1). Qed.
Lemma lem5812589 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term62 _120521 B x op s f) = (@iterate B _120521 op s f).
Proof. exact (@lem5812588 B (term52 _120521 B x op s f) (@iterate B _120521 op s f)). Qed.
Lemma lem5812590 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term53 _120521 B x op s f) = (@iterate B _120521 op s f).
Proof. exact (TRANS (@lem5812585 _120521 B op f x s h1) (@lem5812589 _120521 B x op s f)). Qed.
Lemma lem5812591 {_120521 B : Type'} (op : type1400 B) (x : _120521) (s : _120521 -> Prop) (f : _120521 -> B) : (term55 _120521 B op x s f) = (term55 _120521 B op x s f).
Proof. exact (eq_refl (term55 _120521 B op x s f)). Qed.
Lemma lem5812592 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : ((term56 _120521 B op x s f) = (term53 _120521 B x op s f)) = ((term56 _120521 B op x s f) = (@iterate B _120521 op s f)).
Proof. exact (MK_COMB (@lem5812591 _120521 B op x s f) (@lem5812590 _120521 B op f x s h1)). Qed.
Lemma lem5812595 {_120521 : Type'} (s : _120521 -> Prop) : (term57 _120521 s) = (term57 _120521 s).
Proof. exact (eq_refl (term57 _120521 s)). Qed.
Lemma lem5812596 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) (x : _120521) (s : _120521 -> Prop) (h1 : (@IN _120521 x s) = True) : (term58 _120521 B x op s f) = (term63 _120521 B x op s f).
Proof. exact (MK_COMB (@lem5812595 _120521 s) (@lem5812592 _120521 B op f x s h1)). Qed.
Lemma lem5812599 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term64 _120521 B x op s f.
Proof. exact (fun h0 : (@IN _120521 x s) = True => @lem5812596 _120521 B op f x s h0). Qed.
Lemma lem5812600 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term65 _120521 B x op s f.
Proof. exact (conj (@lem5812577 _120521 B x op s f) (@lem5812599 _120521 B x op s f)). Qed.
Lemma lem5812602 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term66 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5812603 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : term67 _120521 B x op s f.
Proof. exact (@lem5812602 (term58 _120521 B x op s f) (term63 _120521 B x op s f) (@IN _120521 x s) (term59 _120521 B x op s f)). Qed.
Lemma lem5812644 {_120521 B : Type'} (x : _120521) (op : type1400 B) (s : _120521 -> Prop) (f : _120521 -> B) : (term58 _120521 B x op s f) = (term68 _120521 B x op s f).
Proof. exact (@lem5812603 _120521 B x op s f (@lem5812600 _120521 B x op s f)). Qed.
Lemma lem5812645 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term69 _120521 B x op f) = (term70 _120521 B x op f).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5812644 _120521 B x op s f)). Qed.
Lemma lem5812646 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5812647 {_120521 B : Type'} (x : _120521) (op : type1400 B) (f : _120521 -> B) : (term71 _120521 B x op f) = (term72 _120521 B x op f).
Proof. exact (MK_COMB (@lem5812646 _120521) (@lem5812645 _120521 B x op f)). Qed.
Lemma lem5812648 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term73 _120521 B op f) = (term74 _120521 B op f).
Proof. exact (fun_ext (fun x : _120521 => @lem5812647 _120521 B x op f)). Qed.
Lemma lem5812649 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5812650 {_120521 B : Type'} (op : type1400 B) (f : _120521 -> B) : (term75 _120521 B op f) = (term76 _120521 B op f).
Proof. exact (MK_COMB (@lem5812649 _120521) (@lem5812648 _120521 B op f)). Qed.
Lemma lem5812651 {_120521 B : Type'} (op : type1400 B) : (term77 _120521 B op) = (term78 _120521 B op).
Proof. exact (fun_ext (fun f : _120521 -> B => @lem5812650 _120521 B op f)). Qed.
Lemma lem5812652 {_120521 B : Type'} : (@all (_120521 -> B)) = (@all (_120521 -> B)).
Proof. exact (eq_refl (@all (_120521 -> B))). Qed.
Lemma lem5812653 {_120521 B : Type'} (op : type1400 B) : (term79 _120521 B op) = (term80 _120521 B op).
Proof. exact (MK_COMB (@lem5812652 _120521 B) (@lem5812651 _120521 B op)). Qed.
Lemma lem5812654 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)) = ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)).
Proof. exact (eq_refl ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op))). Qed.
Lemma lem5812655 {_120477 B : Type'} (op : type1400 B) : (term81 _120477 B op) = (term81 _120477 B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5812654 _120477 B f op)). Qed.
Lemma lem5812656 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5812657 {_120477 B : Type'} (op : type1400 B) : (term82 _120477 B op) = (term82 _120477 B op).
Proof. exact (MK_COMB (@lem5812656 _120477 B) (@lem5812655 _120477 B op)). Qed.
Lemma lem5812658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5812659 {_120477 B : Type'} (op : type1400 B) : (term83 _120477 B op) = (term83 _120477 B op).
Proof. exact (MK_COMB (@lem5812658) (@lem5812657 _120477 B op)). Qed.
Lemma lem5812660 {_120477 _120521 B : Type'} (op : type1400 B) : (term93 _120477 _120521 B op) = (term94 _120477 _120521 B op).
Proof. exact (MK_COMB (@lem5812659 _120477 B op) (@lem5812653 _120521 B op)). Qed.
Lemma lem5812663 {B : Type'} (op : type1400 B) : (term86 B op) = (term86 B op).
Proof. exact (eq_refl (term86 B op)). Qed.
Lemma lem5812664 {_120477 _120521 B : Type'} (op : type1400 B) : (term95 _120477 _120521 B op) = (term96 _120477 _120521 B op).
Proof. exact (MK_COMB (@lem5812663 B op) (@lem5812660 _120477 _120521 B op)). Qed.
Lemma lem5812665 {_120477 _120521 B : Type'} : (term97 _120477 _120521 B) = (term98 _120477 _120521 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5812664 _120477 _120521 B op)). Qed.
Lemma lem5812666 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5812667 {_120477 _120521 B : Type'} : (term4 _120477 _120521 B) = (term99 _120477 _120521 B).
Proof. exact (MK_COMB (@lem5812666 B) (@lem5812665 _120477 _120521 B)). Qed.
Lemma lem5812668 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812669 {_120477 _120521 B : Type'} : (term16 _120477 _120521 B) = (term100 _120477 _120521 B).
Proof. exact (MK_COMB (@lem5812668) (@lem5812667 _120477 _120521 B)). Qed.
Lemma lem5812670 {_120477 _120521 A B : Type'} : (term20 _120477 _120521 A B) = (term102 _120477 _120521 A B).
Proof. exact (MK_COMB (@lem5812669 _120477 _120521 B) (@lem5812553 _120477 _120521 A B)). Qed.
Lemma lem5812674 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem5812675 {_120519 : Type'} : (@COND _120519) = (@COND _120519).
Proof. exact (eq_refl (@COND _120519)). Qed.
Lemma lem5812676 {_120519 A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term103 _120519 A x s) = (@COND _120519 False).
Proof. exact (MK_COMB (@lem5812675 _120519) (@lem5812674 A x s h1)). Qed.
Lemma lem5812677 {_120519 A : Type'} (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (@iterate _120519 A op s f) = (@iterate _120519 A op s f).
Proof. exact (eq_refl (@iterate _120519 A op s f)). Qed.
Lemma lem5812678 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term104 _120519 A x op s f) = (term105 _120519 A op s f).
Proof. exact (MK_COMB (@lem5812676 _120519 A x s h1) (@lem5812677 _120519 A op s f)). Qed.
Lemma lem5812679 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term106 _120519 A x op s f) = (term106 _120519 A x op s f).
Proof. exact (eq_refl (term106 _120519 A x op s f)). Qed.
Lemma lem5812680 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term107 _120519 A x op s f) = (term108 _120519 A x op s f).
Proof. exact (MK_COMB (@lem5812678 _120519 A op f x s h1) (@lem5812679 _120519 A x op s f)). Qed.
Lemma lem5812682 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5812683 {_120519 : Type'} (t1 : _120519) (t2 : _120519) : (@COND _120519 False t1 t2) = t2.
Proof. exact (@lem5812682 _120519 t1 t2). Qed.
Lemma lem5812684 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term108 _120519 A x op s f) = (term106 _120519 A x op s f).
Proof. exact (@lem5812683 _120519 (@iterate _120519 A op s f) (term106 _120519 A x op s f)). Qed.
Lemma lem5812685 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term107 _120519 A x op s f) = (term106 _120519 A x op s f).
Proof. exact (TRANS (@lem5812680 _120519 A op f x s h1) (@lem5812684 _120519 A x op s f)). Qed.
Lemma lem5812686 {_120519 A : Type'} (op : type1400 _120519) (x : A) (s : A -> Prop) (f : A -> _120519) : (term109 _120519 A op x s f) = (term109 _120519 A op x s f).
Proof. exact (eq_refl (term109 _120519 A op x s f)). Qed.
Lemma lem5812687 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term110 _120519 A op x s f) = (term107 _120519 A x op s f)) = ((term110 _120519 A op x s f) = (term106 _120519 A x op s f)).
Proof. exact (MK_COMB (@lem5812686 _120519 A op x s f) (@lem5812685 _120519 A op f x s h1)). Qed.
Lemma lem5812690 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem5812691 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term111 _120519 A x op s f) = (term112 _120519 A x op s f).
Proof. exact (MK_COMB (@lem5812690 A s) (@lem5812687 _120519 A op f x s h1)). Qed.
Lemma lem5812694 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : term113 _120519 A x op s f.
Proof. exact (fun h0 : (@IN A x s) = False => @lem5812691 _120519 A op f x s h0). Qed.
Lemma lem5812696 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem5812697 {_120519 : Type'} : (@COND _120519) = (@COND _120519).
Proof. exact (eq_refl (@COND _120519)). Qed.
Lemma lem5812698 {_120519 A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term103 _120519 A x s) = (@COND _120519 True).
Proof. exact (MK_COMB (@lem5812697 _120519) (@lem5812696 A x s h1)). Qed.
Lemma lem5812699 {_120519 A : Type'} (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (@iterate _120519 A op s f) = (@iterate _120519 A op s f).
Proof. exact (eq_refl (@iterate _120519 A op s f)). Qed.
Lemma lem5812700 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term104 _120519 A x op s f) = (term114 _120519 A op s f).
Proof. exact (MK_COMB (@lem5812698 _120519 A x s h1) (@lem5812699 _120519 A op s f)). Qed.
Lemma lem5812701 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term106 _120519 A x op s f) = (term106 _120519 A x op s f).
Proof. exact (eq_refl (term106 _120519 A x op s f)). Qed.
Lemma lem5812702 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term107 _120519 A x op s f) = (term115 _120519 A x op s f).
Proof. exact (MK_COMB (@lem5812700 _120519 A op f x s h1) (@lem5812701 _120519 A x op s f)). Qed.
Lemma lem5812704 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5812705 {_120519 : Type'} (t2 : _120519) (t1 : _120519) : (@COND _120519 True t1 t2) = t1.
Proof. exact (@lem5812704 _120519 t2 t1). Qed.
Lemma lem5812706 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term115 _120519 A x op s f) = (@iterate _120519 A op s f).
Proof. exact (@lem5812705 _120519 (term106 _120519 A x op s f) (@iterate _120519 A op s f)). Qed.
Lemma lem5812707 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term107 _120519 A x op s f) = (@iterate _120519 A op s f).
Proof. exact (TRANS (@lem5812702 _120519 A op f x s h1) (@lem5812706 _120519 A x op s f)). Qed.
Lemma lem5812708 {_120519 A : Type'} (op : type1400 _120519) (x : A) (s : A -> Prop) (f : A -> _120519) : (term109 _120519 A op x s f) = (term109 _120519 A op x s f).
Proof. exact (eq_refl (term109 _120519 A op x s f)). Qed.
Lemma lem5812709 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term110 _120519 A op x s f) = (term107 _120519 A x op s f)) = ((term110 _120519 A op x s f) = (@iterate _120519 A op s f)).
Proof. exact (MK_COMB (@lem5812708 _120519 A op x s f) (@lem5812707 _120519 A op f x s h1)). Qed.
Lemma lem5812712 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem5812713 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term111 _120519 A x op s f) = (term116 _120519 A x op s f).
Proof. exact (MK_COMB (@lem5812712 A s) (@lem5812709 _120519 A op f x s h1)). Qed.
Lemma lem5812716 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : term117 _120519 A x op s f.
Proof. exact (fun h0 : (@IN A x s) = True => @lem5812713 _120519 A op f x s h0). Qed.
Lemma lem5812717 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : term118 _120519 A x op s f.
Proof. exact (conj (@lem5812694 _120519 A x op s f) (@lem5812716 _120519 A x op s f)). Qed.
Lemma lem5812719 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term66 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5812720 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : term119 _120519 A x op s f.
Proof. exact (@lem5812719 (term111 _120519 A x op s f) (term116 _120519 A x op s f) (@IN A x s) (term112 _120519 A x op s f)). Qed.
Lemma lem5812761 {_120519 A : Type'} (x : A) (op : type1400 _120519) (s : A -> Prop) (f : A -> _120519) : (term111 _120519 A x op s f) = (term120 _120519 A x op s f).
Proof. exact (@lem5812720 _120519 A x op s f (@lem5812717 _120519 A x op s f)). Qed.
Lemma lem5812762 {_120519 A : Type'} (x : A) (op : type1400 _120519) (f : A -> _120519) : (term121 _120519 A x op f) = (term122 _120519 A x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5812761 _120519 A x op s f)). Qed.
Lemma lem5812763 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5812764 {_120519 A : Type'} (x : A) (op : type1400 _120519) (f : A -> _120519) : (term123 _120519 A x op f) = (term124 _120519 A x op f).
Proof. exact (MK_COMB (@lem5812763 A) (@lem5812762 _120519 A x op f)). Qed.
Lemma lem5812765 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) : (term125 _120519 A op f) = (term126 _120519 A op f).
Proof. exact (fun_ext (fun x : A => @lem5812764 _120519 A x op f)). Qed.
Lemma lem5812766 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5812767 {_120519 A : Type'} (op : type1400 _120519) (f : A -> _120519) : (term127 _120519 A op f) = (term128 _120519 A op f).
Proof. exact (MK_COMB (@lem5812766 A) (@lem5812765 _120519 A op f)). Qed.
Lemma lem5812768 {_120519 A : Type'} (op : type1400 _120519) : (term129 _120519 A op) = (term130 _120519 A op).
Proof. exact (fun_ext (fun f : A -> _120519 => @lem5812767 _120519 A op f)). Qed.
Lemma lem5812769 {_120519 A : Type'} : (@all (A -> _120519)) = (@all (A -> _120519)).
Proof. exact (eq_refl (@all (A -> _120519))). Qed.
Lemma lem5812770 {_120519 A : Type'} (op : type1400 _120519) : (term131 _120519 A op) = (term132 _120519 A op).
Proof. exact (MK_COMB (@lem5812769 _120519 A) (@lem5812768 _120519 A op)). Qed.
Lemma lem5812771 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op))). Qed.
Lemma lem5812772 {_120477 _120519 : Type'} (op : type1400 _120519) : (term81 _120477 _120519 op) = (term81 _120477 _120519 op).
Proof. exact (fun_ext (fun f : _120477 -> _120519 => @lem5812771 _120477 _120519 f op)). Qed.
Lemma lem5812773 {_120477 _120519 : Type'} : (@all (_120477 -> _120519)) = (@all (_120477 -> _120519)).
Proof. exact (eq_refl (@all (_120477 -> _120519))). Qed.
Lemma lem5812774 {_120477 _120519 : Type'} (op : type1400 _120519) : (term82 _120477 _120519 op) = (term82 _120477 _120519 op).
Proof. exact (MK_COMB (@lem5812773 _120477 _120519) (@lem5812772 _120477 _120519 op)). Qed.
Lemma lem5812775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5812776 {_120477 _120519 : Type'} (op : type1400 _120519) : (term83 _120477 _120519 op) = (term83 _120477 _120519 op).
Proof. exact (MK_COMB (@lem5812775) (@lem5812774 _120477 _120519 op)). Qed.
Lemma lem5812777 {_120477 _120519 A : Type'} (op : type1400 _120519) : (term133 _120477 _120519 A op) = (term134 _120477 _120519 A op).
Proof. exact (MK_COMB (@lem5812776 _120477 _120519 op) (@lem5812770 _120519 A op)). Qed.
Lemma lem5812780 {_120519 : Type'} (op : type1400 _120519) : (term86 _120519 op) = (term86 _120519 op).
Proof. exact (eq_refl (term86 _120519 op)). Qed.
Lemma lem5812781 {_120477 _120519 A : Type'} (op : type1400 _120519) : (term135 _120477 _120519 A op) = (term136 _120477 _120519 A op).
Proof. exact (MK_COMB (@lem5812780 _120519 op) (@lem5812777 _120477 _120519 A op)). Qed.
Lemma lem5812782 {_120477 _120519 A : Type'} : (term137 _120477 _120519 A) = (term138 _120477 _120519 A).
Proof. exact (fun_ext (fun op : type1400 _120519 => @lem5812781 _120477 _120519 A op)). Qed.
Lemma lem5812783 {_120519 : Type'} : (@all (_120519 -> _120519 -> _120519)) = (@all (_120519 -> _120519 -> _120519)).
Proof. exact (eq_refl (@all (_120519 -> _120519 -> _120519))). Qed.
Lemma lem5812784 {_120477 _120519 A : Type'} : (term6 _120477 _120519 A) = (term139 _120477 _120519 A).
Proof. exact (MK_COMB (@lem5812783 _120519) (@lem5812782 _120477 _120519 A)). Qed.
Lemma lem5812785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812786 {_120477 _120519 A : Type'} : (term21 _120477 _120519 A) = (term140 _120477 _120519 A).
Proof. exact (MK_COMB (@lem5812785) (@lem5812784 _120477 _120519 A)). Qed.
Lemma lem5812787 {_120477 _120519 _120521 A B : Type'} : (term23 _120477 _120519 _120521 A B) = (term141 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812786 _120477 _120519 A) (@lem5812670 _120477 _120521 A B)). Qed.
Lemma lem5812792 {A : Type'} (x : A) (s : A -> Prop) : ((term142 A s x) = (@FINITE A s)) = ((term142 A s x) = (@FINITE A s)).
Proof. exact (eq_refl ((term142 A s x) = (@FINITE A s))). Qed.
Lemma lem5812793 {A : Type'} (s : A -> Prop) : (term143 A s) = (term143 A s).
Proof. exact (fun_ext (fun x : A => @lem5812792 A x s)). Qed.
Lemma lem5812794 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5812795 {A : Type'} (s : A -> Prop) : (term144 A s) = (term144 A s).
Proof. exact (MK_COMB (@lem5812794 A) (@lem5812793 A s)). Qed.
Lemma lem5812796 {A : Type'} : (term145 A) = (term145 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5812795 A s)). Qed.
Lemma lem5812797 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5812798 {A : Type'} : (term7 A) = (term7 A).
Proof. exact (MK_COMB (@lem5812797 A) (@lem5812796 A)). Qed.
Lemma lem5812799 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812800 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem5812799) (@lem5812798 A)). Qed.
Lemma lem5812801 {_120477 _120519 _120521 A B : Type'} : (term26 _120477 _120519 _120521 A B) = (term146 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812800 A) (@lem5812787 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812806 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : ((term142 _120521 s x) = (@FINITE _120521 s)) = ((term142 _120521 s x) = (@FINITE _120521 s)).
Proof. exact (eq_refl ((term142 _120521 s x) = (@FINITE _120521 s))). Qed.
Lemma lem5812807 {_120521 : Type'} (s : _120521 -> Prop) : (term143 _120521 s) = (term143 _120521 s).
Proof. exact (fun_ext (fun x : _120521 => @lem5812806 _120521 x s)). Qed.
Lemma lem5812808 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5812809 {_120521 : Type'} (s : _120521 -> Prop) : (term144 _120521 s) = (term144 _120521 s).
Proof. exact (MK_COMB (@lem5812808 _120521) (@lem5812807 _120521 s)). Qed.
Lemma lem5812810 {_120521 : Type'} : (term145 _120521) = (term145 _120521).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5812809 _120521 s)). Qed.
Lemma lem5812811 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5812812 {_120521 : Type'} : (term7 _120521) = (term7 _120521).
Proof. exact (MK_COMB (@lem5812811 _120521) (@lem5812810 _120521)). Qed.
Lemma lem5812813 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812814 {_120521 : Type'} : (term24 _120521) = (term24 _120521).
Proof. exact (MK_COMB (@lem5812813) (@lem5812812 _120521)). Qed.
Lemma lem5812815 {_120477 _120519 _120521 A B : Type'} : (term28 _120477 _120519 _120521 A B) = (term147 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812814 _120521) (@lem5812801 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812826 {B : Type'} (s : B -> Prop) (x : B) (y : B) : ((term148 B x s y) = (term149 B s x y)) = ((term148 B x s y) = (term149 B s x y)).
Proof. exact (eq_refl ((term148 B x s y) = (term149 B s x y))). Qed.
Lemma lem5812827 {B : Type'} (s : B -> Prop) (x : B) : (term150 B s x) = (term150 B s x).
Proof. exact (fun_ext (fun y : B => @lem5812826 B s x y)). Qed.
Lemma lem5812828 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5812829 {B : Type'} (s : B -> Prop) (x : B) : (term151 B s x) = (term151 B s x).
Proof. exact (MK_COMB (@lem5812828 B) (@lem5812827 B s x)). Qed.
Lemma lem5812830 {B : Type'} (s : B -> Prop) : (term152 B s) = (term152 B s).
Proof. exact (fun_ext (fun x : B => @lem5812829 B s x)). Qed.
Lemma lem5812831 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5812832 {B : Type'} (s : B -> Prop) : (term153 B s) = (term153 B s).
Proof. exact (MK_COMB (@lem5812831 B) (@lem5812830 B s)). Qed.
Lemma lem5812833 {B : Type'} : (term154 B) = (term154 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5812832 B s)). Qed.
Lemma lem5812834 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5812835 {B : Type'} : (term8 B) = (term8 B).
Proof. exact (MK_COMB (@lem5812834 B) (@lem5812833 B)). Qed.
Lemma lem5812836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812837 {B : Type'} : (term29 B) = (term29 B).
Proof. exact (MK_COMB (@lem5812836) (@lem5812835 B)). Qed.
Lemma lem5812838 {_120477 _120519 _120521 A B : Type'} : (term31 _120477 _120519 _120521 A B) = (term155 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812837 B) (@lem5812815 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812849 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term148 A x s y) = (term149 A s x y)) = ((term148 A x s y) = (term149 A s x y)).
Proof. exact (eq_refl ((term148 A x s y) = (term149 A s x y))). Qed.
Lemma lem5812850 {A : Type'} (s : A -> Prop) (x : A) : (term150 A s x) = (term150 A s x).
Proof. exact (fun_ext (fun y : A => @lem5812849 A s x y)). Qed.
Lemma lem5812851 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5812852 {A : Type'} (s : A -> Prop) (x : A) : (term151 A s x) = (term151 A s x).
Proof. exact (MK_COMB (@lem5812851 A) (@lem5812850 A s x)). Qed.
Lemma lem5812853 {A : Type'} (s : A -> Prop) : (term152 A s) = (term152 A s).
Proof. exact (fun_ext (fun x : A => @lem5812852 A s x)). Qed.
Lemma lem5812854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5812855 {A : Type'} (s : A -> Prop) : (term153 A s) = (term153 A s).
Proof. exact (MK_COMB (@lem5812854 A) (@lem5812853 A s)). Qed.
Lemma lem5812856 {A : Type'} : (term154 A) = (term154 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5812855 A s)). Qed.
Lemma lem5812857 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5812858 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem5812857 A) (@lem5812856 A)). Qed.
Lemma lem5812859 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812860 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem5812859) (@lem5812858 A)). Qed.
Lemma lem5812861 {_120477 _120519 _120521 A B : Type'} : (term33 _120477 _120519 _120521 A B) = (term156 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812860 A) (@lem5812838 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812872 {_120521 : Type'} (s : _120521 -> Prop) (x : _120521) (y : _120521) : ((term148 _120521 x s y) = (term149 _120521 s x y)) = ((term148 _120521 x s y) = (term149 _120521 s x y)).
Proof. exact (eq_refl ((term148 _120521 x s y) = (term149 _120521 s x y))). Qed.
Lemma lem5812873 {_120521 : Type'} (s : _120521 -> Prop) (x : _120521) : (term150 _120521 s x) = (term150 _120521 s x).
Proof. exact (fun_ext (fun y : _120521 => @lem5812872 _120521 s x y)). Qed.
Lemma lem5812874 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5812875 {_120521 : Type'} (s : _120521 -> Prop) (x : _120521) : (term151 _120521 s x) = (term151 _120521 s x).
Proof. exact (MK_COMB (@lem5812874 _120521) (@lem5812873 _120521 s x)). Qed.
Lemma lem5812876 {_120521 : Type'} (s : _120521 -> Prop) : (term152 _120521 s) = (term152 _120521 s).
Proof. exact (fun_ext (fun x : _120521 => @lem5812875 _120521 s x)). Qed.
Lemma lem5812877 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5812878 {_120521 : Type'} (s : _120521 -> Prop) : (term153 _120521 s) = (term153 _120521 s).
Proof. exact (MK_COMB (@lem5812877 _120521) (@lem5812876 _120521 s)). Qed.
Lemma lem5812879 {_120521 : Type'} : (term154 _120521) = (term154 _120521).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5812878 _120521 s)). Qed.
Lemma lem5812880 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5812881 {_120521 : Type'} : (term8 _120521) = (term8 _120521).
Proof. exact (MK_COMB (@lem5812880 _120521) (@lem5812879 _120521)). Qed.
Lemma lem5812882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812883 {_120521 : Type'} : (term29 _120521) = (term29 _120521).
Proof. exact (MK_COMB (@lem5812882) (@lem5812881 _120521)). Qed.
Lemma lem5812884 {_120477 _120519 _120521 A B : Type'} : (term35 _120477 _120519 _120521 A B) = (term157 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812883 _120521) (@lem5812861 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812895 {_120519 : Type'} (s : _120519 -> Prop) (x : _120519) (y : _120519) : ((term148 _120519 x s y) = (term149 _120519 s x y)) = ((term148 _120519 x s y) = (term149 _120519 s x y)).
Proof. exact (eq_refl ((term148 _120519 x s y) = (term149 _120519 s x y))). Qed.
Lemma lem5812896 {_120519 : Type'} (s : _120519 -> Prop) (x : _120519) : (term150 _120519 s x) = (term150 _120519 s x).
Proof. exact (fun_ext (fun y : _120519 => @lem5812895 _120519 s x y)). Qed.
Lemma lem5812897 {_120519 : Type'} : (@all _120519) = (@all _120519).
Proof. exact (eq_refl (@all _120519)). Qed.
Lemma lem5812898 {_120519 : Type'} (s : _120519 -> Prop) (x : _120519) : (term151 _120519 s x) = (term151 _120519 s x).
Proof. exact (MK_COMB (@lem5812897 _120519) (@lem5812896 _120519 s x)). Qed.
Lemma lem5812899 {_120519 : Type'} (s : _120519 -> Prop) : (term152 _120519 s) = (term152 _120519 s).
Proof. exact (fun_ext (fun x : _120519 => @lem5812898 _120519 s x)). Qed.
Lemma lem5812900 {_120519 : Type'} : (@all _120519) = (@all _120519).
Proof. exact (eq_refl (@all _120519)). Qed.
Lemma lem5812901 {_120519 : Type'} (s : _120519 -> Prop) : (term153 _120519 s) = (term153 _120519 s).
Proof. exact (MK_COMB (@lem5812900 _120519) (@lem5812899 _120519 s)). Qed.
Lemma lem5812902 {_120519 : Type'} : (term154 _120519) = (term154 _120519).
Proof. exact (fun_ext (fun s : _120519 -> Prop => @lem5812901 _120519 s)). Qed.
Lemma lem5812903 {_120519 : Type'} : (@all (_120519 -> Prop)) = (@all (_120519 -> Prop)).
Proof. exact (eq_refl (@all (_120519 -> Prop))). Qed.
Lemma lem5812904 {_120519 : Type'} : (term8 _120519) = (term8 _120519).
Proof. exact (MK_COMB (@lem5812903 _120519) (@lem5812902 _120519)). Qed.
Lemma lem5812905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812906 {_120519 : Type'} : (term29 _120519) = (term29 _120519).
Proof. exact (MK_COMB (@lem5812905) (@lem5812904 _120519)). Qed.
Lemma lem5812907 {_120477 _120519 _120521 A B : Type'} : (term37 _120477 _120519 _120521 A B) = (term158 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812906 _120519) (@lem5812884 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812912 {B : Type'} (x : B) (s : B -> Prop) : (term159 B x s) = (term159 B x s).
Proof. exact (eq_refl (term159 B x s)). Qed.
Lemma lem5812913 {B : Type'} (x : B) : (term160 B x) = (term160 B x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5812912 B x s)). Qed.
Lemma lem5812914 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5812915 {B : Type'} (x : B) : (term161 B x) = (term161 B x).
Proof. exact (MK_COMB (@lem5812914 B) (@lem5812913 B x)). Qed.
Lemma lem5812916 {B : Type'} : (term162 B) = (term162 B).
Proof. exact (fun_ext (fun x : B => @lem5812915 B x)). Qed.
Lemma lem5812917 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5812918 {B : Type'} : (term9 B) = (term9 B).
Proof. exact (MK_COMB (@lem5812917 B) (@lem5812916 B)). Qed.
Lemma lem5812919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812920 {B : Type'} : (term38 B) = (term38 B).
Proof. exact (MK_COMB (@lem5812919) (@lem5812918 B)). Qed.
Lemma lem5812921 {_120477 _120519 _120521 A B : Type'} : (term40 _120477 _120519 _120521 A B) = (term163 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812920 B) (@lem5812907 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812926 {A : Type'} (x : A) (s : A -> Prop) : (term159 A x s) = (term159 A x s).
Proof. exact (eq_refl (term159 A x s)). Qed.
Lemma lem5812927 {A : Type'} (x : A) : (term160 A x) = (term160 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5812926 A x s)). Qed.
Lemma lem5812928 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5812929 {A : Type'} (x : A) : (term161 A x) = (term161 A x).
Proof. exact (MK_COMB (@lem5812928 A) (@lem5812927 A x)). Qed.
Lemma lem5812930 {A : Type'} : (term162 A) = (term162 A).
Proof. exact (fun_ext (fun x : A => @lem5812929 A x)). Qed.
Lemma lem5812931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5812932 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (MK_COMB (@lem5812931 A) (@lem5812930 A)). Qed.
Lemma lem5812933 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812934 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (MK_COMB (@lem5812933) (@lem5812932 A)). Qed.
Lemma lem5812935 {_120477 _120519 _120521 A B : Type'} : (term42 _120477 _120519 _120521 A B) = (term164 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812934 A) (@lem5812921 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812940 {_120521 : Type'} (x : _120521) (s : _120521 -> Prop) : (term159 _120521 x s) = (term159 _120521 x s).
Proof. exact (eq_refl (term159 _120521 x s)). Qed.
Lemma lem5812941 {_120521 : Type'} (x : _120521) : (term160 _120521 x) = (term160 _120521 x).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5812940 _120521 x s)). Qed.
Lemma lem5812942 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5812943 {_120521 : Type'} (x : _120521) : (term161 _120521 x) = (term161 _120521 x).
Proof. exact (MK_COMB (@lem5812942 _120521) (@lem5812941 _120521 x)). Qed.
Lemma lem5812944 {_120521 : Type'} : (term162 _120521) = (term162 _120521).
Proof. exact (fun_ext (fun x : _120521 => @lem5812943 _120521 x)). Qed.
Lemma lem5812945 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5812946 {_120521 : Type'} : (term9 _120521) = (term9 _120521).
Proof. exact (MK_COMB (@lem5812945 _120521) (@lem5812944 _120521)). Qed.
Lemma lem5812947 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812948 {_120521 : Type'} : (term38 _120521) = (term38 _120521).
Proof. exact (MK_COMB (@lem5812947) (@lem5812946 _120521)). Qed.
Lemma lem5812949 {_120477 _120519 _120521 A B : Type'} : (term44 _120477 _120519 _120521 A B) = (term165 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812948 _120521) (@lem5812935 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812954 {_120519 : Type'} (x : _120519) (s : _120519 -> Prop) : (term159 _120519 x s) = (term159 _120519 x s).
Proof. exact (eq_refl (term159 _120519 x s)). Qed.
Lemma lem5812955 {_120519 : Type'} (x : _120519) : (term160 _120519 x) = (term160 _120519 x).
Proof. exact (fun_ext (fun s : _120519 -> Prop => @lem5812954 _120519 x s)). Qed.
Lemma lem5812956 {_120519 : Type'} : (@all (_120519 -> Prop)) = (@all (_120519 -> Prop)).
Proof. exact (eq_refl (@all (_120519 -> Prop))). Qed.
Lemma lem5812957 {_120519 : Type'} (x : _120519) : (term161 _120519 x) = (term161 _120519 x).
Proof. exact (MK_COMB (@lem5812956 _120519) (@lem5812955 _120519 x)). Qed.
Lemma lem5812958 {_120519 : Type'} : (term162 _120519) = (term162 _120519).
Proof. exact (fun_ext (fun x : _120519 => @lem5812957 _120519 x)). Qed.
Lemma lem5812959 {_120519 : Type'} : (@all _120519) = (@all _120519).
Proof. exact (eq_refl (@all _120519)). Qed.
Lemma lem5812960 {_120519 : Type'} : (term9 _120519) = (term9 _120519).
Proof. exact (MK_COMB (@lem5812959 _120519) (@lem5812958 _120519)). Qed.
Lemma lem5812961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812962 {_120519 : Type'} : (term38 _120519) = (term38 _120519).
Proof. exact (MK_COMB (@lem5812961) (@lem5812960 _120519)). Qed.
Lemma lem5812963 {_120477 _120519 _120521 A B : Type'} : (term46 _120477 _120519 _120521 A B) = (term166 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812962 _120519) (@lem5812949 _120477 _120519 _120521 A B)). Qed.
Lemma lem5812972 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term167 A B a op s f) = (term167 A B a op s f).
Proof. exact (eq_refl (term167 A B a op s f)). Qed.
Lemma lem5812973 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term168 A B op s f) = (term168 A B op s f).
Proof. exact (fun_ext (fun a : A => @lem5812972 A B a op s f)). Qed.
Lemma lem5812974 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5812975 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term169 A B op s f) = (term169 A B op s f).
Proof. exact (MK_COMB (@lem5812974 A) (@lem5812973 A B op s f)). Qed.
Lemma lem5812976 {A B : Type'} (op : type1400 B) (f : A -> B) : (term170 A B op f) = (term170 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5812975 A B op s f)). Qed.
Lemma lem5812977 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5812978 {A B : Type'} (op : type1400 B) (f : A -> B) : (term171 A B op f) = (term171 A B op f).
Proof. exact (MK_COMB (@lem5812977 A) (@lem5812976 A B op f)). Qed.
Lemma lem5812979 {A B : Type'} (op : type1400 B) : (term172 A B op) = (term172 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5812978 A B op f)). Qed.
Lemma lem5812980 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5812981 {A B : Type'} (op : type1400 B) : (term173 A B op) = (term173 A B op).
Proof. exact (MK_COMB (@lem5812980 A B) (@lem5812979 A B op)). Qed.
Lemma lem5812984 {B : Type'} (op : type1400 B) : (term86 B op) = (term86 B op).
Proof. exact (eq_refl (term86 B op)). Qed.
Lemma lem5812985 {A B : Type'} (op : type1400 B) : (term174 A B op) = (term174 A B op).
Proof. exact (MK_COMB (@lem5812984 B op) (@lem5812981 A B op)). Qed.
Lemma lem5812986 {A B : Type'} : (term175 A B) = (term175 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5812985 A B op)). Qed.
Lemma lem5812987 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5812988 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (MK_COMB (@lem5812987 B) (@lem5812986 A B)). Qed.
Lemma lem5812989 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5812990 {A B : Type'} : (term3 A B) = (term3 A B).
Proof. exact (MK_COMB (@lem5812989) (@lem5812988 A B)). Qed.
Lemma lem5812991 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5812992 {A B : Type'} : (term47 A B) = (term47 A B).
Proof. exact (MK_COMB (@lem5812991) (@lem5812990 A B)). Qed.
Lemma lem5812993 {_120477 _120519 _120521 A B : Type'} : (term48 _120477 _120519 _120521 A B) = (term176 _120477 _120519 _120521 A B).
Proof. exact (MK_COMB (@lem5812992 A B) (@lem5812963 _120477 _120519 _120521 A B)). Qed.
Lemma lem5813390 {_120477 _120519 _120521 A B : Type'} : (term10 _120477 _120519 _120521 A B) = (term176 _120477 _120519 _120521 A B).
Proof. exact (TRANS (@lem5812320 _120477 _120519 _120521 A B) (@lem5812993 _120477 _120519 _120521 A B)). Qed.
Lemma lem5813391 {_120477 _120519 _120521 A B : Type'} : (term176 _120477 _120519 _120521 A B) = (term10 _120477 _120519 _120521 A B).
Proof. exact (SYM (@lem5813390 _120477 _120519 _120521 A B)). Qed.
Lemma lem5813392 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem5813395 {A : Type'} (h1 : term9 A) : term9 A.
Proof. exact (h1). Qed.
Lemma lem5813399 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem5813402 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem5813405 {_120477 A B : Type'} (h1 : term99 _120477 A B) : term99 _120477 A B.
Proof. exact (h1). Qed.
Lemma lem5813418 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term177 A B a op s f) = (term178 A B a op s f).
Proof. exact (@lem17362 (term179 A a s) ((term180 A B op s a f) = (@iterate B A op s f))). Qed.
Lemma lem5813419 {A : Type'} (P : A -> Prop) : (term181 A P) = (term182 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5813420 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term183 A B op s f) = (term184 A B op s f).
Proof. exact (@lem5813419 A (term168 A B op s f)). Qed.
Lemma lem5813421 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term185 A B op s f a) = (term167 A B a op s f).
Proof. exact (eq_refl (term185 A B op s f a)). Qed.
Lemma lem5813422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5813423 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term186 A B op s f a) = (term177 A B a op s f).
Proof. exact (MK_COMB (@lem5813422) (@lem5813421 A B a op s f)). Qed.
Lemma lem5813424 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term186 A B op s f a) = (term178 A B a op s f).
Proof. exact (TRANS (@lem5813423 A B a op s f) (@lem5813418 A B a op s f)). Qed.
Lemma lem5813425 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term187 A B op s f) = (term188 A B op s f).
Proof. exact (fun_ext (fun a : A => @lem5813424 A B a op s f)). Qed.
Lemma lem5813426 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5813427 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term184 A B op s f) = (term189 A B op s f).
Proof. exact (MK_COMB (@lem5813426 A) (@lem5813425 A B op s f)). Qed.
Lemma lem5813428 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term183 A B op s f) = (term189 A B op s f).
Proof. exact (TRANS (@lem5813420 A B op s f) (@lem5813427 A B op s f)). Qed.
Lemma lem5813429 {A : Type'} (P : type686 A) : (term190 A P) = (term191 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem5813430 {A B : Type'} (op : type1400 B) (f : A -> B) : (term192 A B op f) = (term193 A B op f).
Proof. exact (@lem5813429 A (term170 A B op f)). Qed.
Lemma lem5813431 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term194 A B op f s) = (term169 A B op s f).
Proof. exact (eq_refl (term194 A B op f s)). Qed.
Lemma lem5813432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5813433 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term195 A B op f s) = (term183 A B op s f).
Proof. exact (MK_COMB (@lem5813432) (@lem5813431 A B op s f)). Qed.
Lemma lem5813434 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term195 A B op f s) = (term189 A B op s f).
Proof. exact (TRANS (@lem5813433 A B op s f) (@lem5813428 A B op s f)). Qed.
Lemma lem5813435 {A B : Type'} (op : type1400 B) (f : A -> B) : (term196 A B op f) = (term197 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5813434 A B op s f)). Qed.
Lemma lem5813436 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5813437 {A B : Type'} (op : type1400 B) (f : A -> B) : (term193 A B op f) = (term198 A B op f).
Proof. exact (MK_COMB (@lem5813436 A) (@lem5813435 A B op f)). Qed.
Lemma lem5813438 {A B : Type'} (op : type1400 B) (f : A -> B) : (term192 A B op f) = (term198 A B op f).
Proof. exact (TRANS (@lem5813430 A B op f) (@lem5813437 A B op f)). Qed.
Lemma lem5813439 {A B : Type'} (P : type572 A B) : (term199 A B P) = (term200 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem5813440 {A B : Type'} (op : type1400 B) : (term201 A B op) = (term202 A B op).
Proof. exact (@lem5813439 A B (term172 A B op)). Qed.
Lemma lem5813441 {A B : Type'} (op : type1400 B) (f : A -> B) : (term203 A B op f) = (term171 A B op f).
Proof. exact (eq_refl (term203 A B op f)). Qed.
Lemma lem5813442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5813443 {A B : Type'} (op : type1400 B) (f : A -> B) : (term204 A B op f) = (term192 A B op f).
Proof. exact (MK_COMB (@lem5813442) (@lem5813441 A B op f)). Qed.
Lemma lem5813444 {A B : Type'} (op : type1400 B) (f : A -> B) : (term204 A B op f) = (term198 A B op f).
Proof. exact (TRANS (@lem5813443 A B op f) (@lem5813438 A B op f)). Qed.
Lemma lem5813445 {A B : Type'} (op : type1400 B) : (term205 A B op) = (term206 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5813444 A B op f)). Qed.
Lemma lem5813446 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5813447 {A B : Type'} (op : type1400 B) : (term202 A B op) = (term207 A B op).
Proof. exact (MK_COMB (@lem5813446 A B) (@lem5813445 A B op)). Qed.
Lemma lem5813448 {A B : Type'} (op : type1400 B) : (term201 A B op) = (term207 A B op).
Proof. exact (TRANS (@lem5813440 A B op) (@lem5813447 A B op)). Qed.
Lemma lem5813450 {B : Type'} (op : type1400 B) : (term208 B op) = (term208 B op).
Proof. exact (eq_refl (term208 B op)). Qed.
Lemma lem5813451 {A B : Type'} (op : type1400 B) : (term209 A B op) = (term210 A B op).
Proof. exact (MK_COMB (@lem5813450 B op) (@lem5813448 A B op)). Qed.
Lemma lem5813452 {A B : Type'} (op : type1400 B) : (term211 A B op) = (term209 A B op).
Proof. exact (@lem17362 (@monoidal B op) (term173 A B op)). Qed.
Lemma lem5813453 {A B : Type'} (op : type1400 B) : (term211 A B op) = (term210 A B op).
Proof. exact (TRANS (@lem5813452 A B op) (@lem5813451 A B op)). Qed.
Lemma lem5813454 {B : Type'} (P : type403 B) : (term212 B P) = (term213 B P).
Proof. exact (@lem18392 (type1400 B) P). Qed.
Lemma lem5813455 {A B : Type'} : (term3 A B) = (term214 A B).
Proof. exact (@lem5813454 B (term175 A B)). Qed.
Lemma lem5813456 {A B : Type'} (op : type1400 B) : (term215 A B op) = (term174 A B op).
Proof. exact (eq_refl (term215 A B op)). Qed.
Lemma lem5813457 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5813458 {A B : Type'} (op : type1400 B) : (term216 A B op) = (term211 A B op).
Proof. exact (MK_COMB (@lem5813457) (@lem5813456 A B op)). Qed.
Lemma lem5813459 {A B : Type'} (op : type1400 B) : (term216 A B op) = (term210 A B op).
Proof. exact (TRANS (@lem5813458 A B op) (@lem5813453 A B op)). Qed.
Lemma lem5813460 {A B : Type'} : (term217 A B) = (term218 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5813459 A B op)). Qed.
Lemma lem5813461 {B : Type'} : (@ex (B -> B -> B)) = (@ex (B -> B -> B)).
Proof. exact (eq_refl (@ex (B -> B -> B))). Qed.
Lemma lem5813462 {A B : Type'} : (term214 A B) = (term219 A B).
Proof. exact (MK_COMB (@lem5813461 B) (@lem5813460 A B)). Qed.
Lemma lem5813463 {A B : Type'} : (term3 A B) = (term219 A B).
Proof. exact (TRANS (@lem5813455 A B) (@lem5813462 A B)). Qed.
Lemma lem5813550 {A : Type'} (P : Prop) (Q : A -> Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5813551 {A B : Type'} (P : Prop) (Q : type572 A B) : (term222 A B P Q) = (term223 A B P Q).
Proof. exact (@lem5813550 (A -> B) P Q). Qed.
Lemma lem5813552 {A B : Type'} (op : type1400 B) : (term224 A B op) = (term225 A B op).
Proof. exact (@lem5813551 A B (@monoidal B op) (term206 A B op)). Qed.
Lemma lem5813553 {A B : Type'} (op : type1400 B) (f : A -> B) : (term226 A B op f) = (term198 A B op f).
Proof. exact (eq_refl (term226 A B op f)). Qed.
Lemma lem5813554 {A B : Type'} (op : type1400 B) : (term227 A B op) = (term206 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5813553 A B op f)). Qed.
Lemma lem5813555 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5813556 {A B : Type'} (op : type1400 B) : (term228 A B op) = (term207 A B op).
Proof. exact (MK_COMB (@lem5813555 A B) (@lem5813554 A B op)). Qed.
Lemma lem5813557 {B : Type'} (op : type1400 B) : (term208 B op) = (term208 B op).
Proof. exact (eq_refl (term208 B op)). Qed.
Lemma lem5813558 {A B : Type'} (op : type1400 B) : (term224 A B op) = (term210 A B op).
Proof. exact (MK_COMB (@lem5813557 B op) (@lem5813556 A B op)). Qed.
Lemma lem5813559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5813560 {A B : Type'} (op : type1400 B) : (term229 A B op) = (term230 A B op).
Proof. exact (MK_COMB (@lem5813559) (@lem5813558 A B op)). Qed.
Lemma lem5813561 {A B : Type'} (op : type1400 B) (f : A -> B) : (term226 A B op f) = (term198 A B op f).
Proof. exact (eq_refl (term226 A B op f)). Qed.
Lemma lem5813562 {B : Type'} (op : type1400 B) : (term208 B op) = (term208 B op).
Proof. exact (eq_refl (term208 B op)). Qed.
Lemma lem5813563 {A B : Type'} (op : type1400 B) (f : A -> B) : (term231 A B op f) = (term232 A B op f).
Proof. exact (MK_COMB (@lem5813562 B op) (@lem5813561 A B op f)). Qed.
Lemma lem5813564 {A B : Type'} (op : type1400 B) : (term233 A B op) = (term234 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5813563 A B op f)). Qed.
Lemma lem5813565 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5813566 {A B : Type'} (op : type1400 B) : (term225 A B op) = (term235 A B op).
Proof. exact (MK_COMB (@lem5813565 A B) (@lem5813564 A B op)). Qed.
Lemma lem5813567 {A B : Type'} (op : type1400 B) : ((term224 A B op) = (term225 A B op)) = ((term210 A B op) = (term235 A B op)).
Proof. exact (MK_COMB (@lem5813560 A B op) (@lem5813566 A B op)). Qed.
Lemma lem5813568 {A B : Type'} (op : type1400 B) : (term210 A B op) = (term235 A B op).
Proof. exact (EQ_MP (@lem5813567 A B op) (@lem5813552 A B op)). Qed.
Lemma lem5813570 {A : Type'} (P : Prop) (Q : A -> Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5813571 {A : Type'} (P : Prop) (Q : type686 A) : (term236 A P Q) = (term237 A P Q).
Proof. exact (@lem5813570 (A -> Prop) P Q). Qed.
Lemma lem5813572 {A B : Type'} (op : type1400 B) (f : A -> B) : (term238 A B op f) = (term239 A B op f).
Proof. exact (@lem5813571 A (@monoidal B op) (term197 A B op f)). Qed.
Lemma lem5813573 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term240 A B op f s) = (term189 A B op s f).
Proof. exact (eq_refl (term240 A B op f s)). Qed.
Lemma lem5813574 {A B : Type'} (op : type1400 B) (f : A -> B) : (term241 A B op f) = (term197 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5813573 A B op s f)). Qed.
Lemma lem5813575 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5813576 {A B : Type'} (op : type1400 B) (f : A -> B) : (term242 A B op f) = (term198 A B op f).
Proof. exact (MK_COMB (@lem5813575 A) (@lem5813574 A B op f)). Qed.
Lemma lem5813577 {B : Type'} (op : type1400 B) : (term208 B op) = (term208 B op).
Proof. exact (eq_refl (term208 B op)). Qed.
Lemma lem5813578 {A B : Type'} (op : type1400 B) (f : A -> B) : (term238 A B op f) = (term232 A B op f).
Proof. exact (MK_COMB (@lem5813577 B op) (@lem5813576 A B op f)). Qed.
Lemma lem5813579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5813580 {A B : Type'} (op : type1400 B) (f : A -> B) : (term243 A B op f) = (term244 A B op f).
Proof. exact (MK_COMB (@lem5813579) (@lem5813578 A B op f)). Qed.
Lemma lem5813581 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term240 A B op f s) = (term189 A B op s f).
Proof. exact (eq_refl (term240 A B op f s)). Qed.
Lemma lem5813582 {B : Type'} (op : type1400 B) : (term208 B op) = (term208 B op).
Proof. exact (eq_refl (term208 B op)). Qed.
Lemma lem5813583 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term245 A B op f s) = (term246 A B op s f).
Proof. exact (MK_COMB (@lem5813582 B op) (@lem5813581 A B op s f)). Qed.
Lemma lem5813584 {A B : Type'} (op : type1400 B) (f : A -> B) : (term247 A B op f) = (term248 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5813583 A B op s f)). Qed.
Lemma lem5813585 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5813586 {A B : Type'} (op : type1400 B) (f : A -> B) : (term239 A B op f) = (term249 A B op f).
Proof. exact (MK_COMB (@lem5813585 A) (@lem5813584 A B op f)). Qed.
Lemma lem5813587 {A B : Type'} (op : type1400 B) (f : A -> B) : ((term238 A B op f) = (term239 A B op f)) = ((term232 A B op f) = (term249 A B op f)).
Proof. exact (MK_COMB (@lem5813580 A B op f) (@lem5813586 A B op f)). Qed.
Lemma lem5813588 {A B : Type'} (op : type1400 B) (f : A -> B) : (term232 A B op f) = (term249 A B op f).
Proof. exact (EQ_MP (@lem5813587 A B op f) (@lem5813572 A B op f)). Qed.
Lemma lem5813590 {A : Type'} (P : Prop) (Q : A -> Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5813591 {A : Type'} (P : Prop) (Q : A -> Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (@lem5813590 A P Q). Qed.
Lemma lem5813592 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term250 A B op s f) = (term251 A B op s f).
Proof. exact (@lem5813591 A (@monoidal B op) (term188 A B op s f)). Qed.
Lemma lem5813593 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term252 A B op s f a) = (term178 A B a op s f).
Proof. exact (eq_refl (term252 A B op s f a)). Qed.
Lemma lem5813594 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term253 A B op s f) = (term188 A B op s f).
Proof. exact (fun_ext (fun a : A => @lem5813593 A B a op s f)). Qed.
Lemma lem5813595 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5813596 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term254 A B op s f) = (term189 A B op s f).
Proof. exact (MK_COMB (@lem5813595 A) (@lem5813594 A B op s f)). Qed.
Lemma lem5813597 {B : Type'} (op : type1400 B) : (term208 B op) = (term208 B op).
Proof. exact (eq_refl (term208 B op)). Qed.
Lemma lem5813598 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term250 A B op s f) = (term246 A B op s f).
Proof. exact (MK_COMB (@lem5813597 B op) (@lem5813596 A B op s f)). Qed.
Lemma lem5813599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5813600 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term255 A B op s f) = (term256 A B op s f).
Proof. exact (MK_COMB (@lem5813599) (@lem5813598 A B op s f)). Qed.
Lemma lem5813601 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term252 A B op s f a) = (term178 A B a op s f).
Proof. exact (eq_refl (term252 A B op s f a)). Qed.
Lemma lem5813602 {B : Type'} (op : type1400 B) : (term208 B op) = (term208 B op).
Proof. exact (eq_refl (term208 B op)). Qed.
Lemma lem5813603 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term257 A B op s f a) = (term258 A B a op s f).
Proof. exact (MK_COMB (@lem5813602 B op) (@lem5813601 A B a op s f)). Qed.
Lemma lem5813604 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term259 A B op s f) = (term260 A B op s f).
Proof. exact (fun_ext (fun a : A => @lem5813603 A B a op s f)). Qed.
Lemma lem5813605 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5813606 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term251 A B op s f) = (term261 A B op s f).
Proof. exact (MK_COMB (@lem5813605 A) (@lem5813604 A B op s f)). Qed.
Lemma lem5813607 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term250 A B op s f) = (term251 A B op s f)) = ((term246 A B op s f) = (term261 A B op s f)).
Proof. exact (MK_COMB (@lem5813600 A B op s f) (@lem5813606 A B op s f)). Qed.
Lemma lem5813608 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term246 A B op s f) = (term261 A B op s f).
Proof. exact (EQ_MP (@lem5813607 A B op s f) (@lem5813592 A B op s f)). Qed.
Lemma lem5813609 {A B : Type'} (op : type1400 B) (f : A -> B) : (term248 A B op f) = (term262 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5813608 A B op s f)). Qed.
Lemma lem5813610 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5813611 {A B : Type'} (op : type1400 B) (f : A -> B) : (term249 A B op f) = (term263 A B op f).
Proof. exact (MK_COMB (@lem5813610 A) (@lem5813609 A B op f)). Qed.
Lemma lem5813612 {A B : Type'} (op : type1400 B) (f : A -> B) : (term232 A B op f) = (term263 A B op f).
Proof. exact (TRANS (@lem5813588 A B op f) (@lem5813611 A B op f)). Qed.
Lemma lem5813613 {A B : Type'} (op : type1400 B) : (term234 A B op) = (term264 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5813612 A B op f)). Qed.
Lemma lem5813614 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5813615 {A B : Type'} (op : type1400 B) : (term235 A B op) = (term265 A B op).
Proof. exact (MK_COMB (@lem5813614 A B) (@lem5813613 A B op)). Qed.
Lemma lem5813616 {A B : Type'} (op : type1400 B) : (term210 A B op) = (term265 A B op).
Proof. exact (TRANS (@lem5813568 A B op) (@lem5813615 A B op)). Qed.
Lemma lem5813617 {A B : Type'} : (term218 A B) = (term266 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5813616 A B op)). Qed.
Lemma lem5813618 {B : Type'} : (@ex (B -> B -> B)) = (@ex (B -> B -> B)).
Proof. exact (eq_refl (@ex (B -> B -> B))). Qed.
Lemma lem5813620 {A B : Type'} : (term219 A B) = (term267 A B).
Proof. exact (MK_COMB (@lem5813618 B) (@lem5813617 A B)). Qed.
Lemma lem5813621 {A B : Type'} : (term3 A B) = (term267 A B).
Proof. exact (TRANS (@lem5813463 A B) (@lem5813620 A B)). Qed.
Lemma lem5813622 {A B : Type'} (h1 : term3 A B) : term267 A B.
Proof. exact (EQ_MP (@lem5813621 A B) (@lem5813392 A B h1)). Qed.
Lemma lem5813769 {A : Type'} (x : A) (s : A -> Prop) : (term159 A x s) = (term268 A x s).
Proof. exact (@lem17265 (@IN A x s) ((term269 A s x) = s)). Qed.
Lemma lem5813770 {A : Type'} (x : A) : (term160 A x) = (term270 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5813769 A x s)). Qed.
Lemma lem5813771 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5813772 {A : Type'} (x : A) : (term161 A x) = (term271 A x).
Proof. exact (MK_COMB (@lem5813771 A) (@lem5813770 A x)). Qed.
Lemma lem5813773 {A : Type'} : (term162 A) = (term272 A).
Proof. exact (fun_ext (fun x : A => @lem5813772 A x)). Qed.
Lemma lem5813774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5813831 {A : Type'} : (term9 A) = (term273 A).
Proof. exact (MK_COMB (@lem5813774 A) (@lem5813773 A)). Qed.
Lemma lem5813832 {A : Type'} (h1 : term9 A) : term273 A.
Proof. exact (EQ_MP (@lem5813831 A) (@lem5813395 A h1)). Qed.
Lemma lem5814808 {A : Type'} (x : A) (y : A) : (term274 A x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem5814810 {A : Type'} (x : A) (s : A -> Prop) : (term275 A x s) = (term275 A x s).
Proof. exact (eq_refl (term275 A x s)). Qed.
Lemma lem5814811 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term276 A s x y) = (term277 A s x y).
Proof. exact (MK_COMB (@lem5814810 A x s) (@lem5814808 A x y)). Qed.
Lemma lem5814812 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term278 A s x y) = (term276 A s x y).
Proof. exact (@lem17045 (@IN A x s) (term279 A x y)). Qed.
Lemma lem5814813 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term278 A s x y) = (term277 A s x y).
Proof. exact (TRANS (@lem5814812 A s x y) (@lem5814811 A s x y)). Qed.
Lemma lem5814819 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term280 A s x y) = (term280 A s x y).
Proof. exact (eq_refl (term280 A s x y)). Qed.
Lemma lem5814821 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term281 A x s y) = (term281 A x s y).
Proof. exact (eq_refl (term281 A x s y)). Qed.
Lemma lem5814822 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term282 A s x y) = (term283 A s x y).
Proof. exact (MK_COMB (@lem5814821 A x s y) (@lem5814813 A s x y)). Qed.
Lemma lem5814823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5814824 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term284 A s x y) = (term285 A s x y).
Proof. exact (MK_COMB (@lem5814823) (@lem5814822 A s x y)). Qed.
Lemma lem5814825 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term286 A s x y) = (term287 A s x y).
Proof. exact (MK_COMB (@lem5814824 A s x y) (@lem5814819 A s x y)). Qed.
Lemma lem5814826 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term148 A x s y) = (term149 A s x y)) = (term286 A s x y).
Proof. exact (@lem17784 (term148 A x s y) (term149 A s x y)). Qed.
Lemma lem5814827 {A : Type'} (s : A -> Prop) (x : A) (y : A) : ((term148 A x s y) = (term149 A s x y)) = (term287 A s x y).
Proof. exact (TRANS (@lem5814826 A s x y) (@lem5814825 A s x y)). Qed.
Lemma lem5814828 {A : Type'} (s : A -> Prop) (x : A) : (term150 A s x) = (term288 A s x).
Proof. exact (fun_ext (fun y : A => @lem5814827 A s x y)). Qed.
Lemma lem5814829 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814830 {A : Type'} (s : A -> Prop) (x : A) : (term151 A s x) = (term289 A s x).
Proof. exact (MK_COMB (@lem5814829 A) (@lem5814828 A s x)). Qed.
Lemma lem5814831 {A : Type'} (s : A -> Prop) : (term152 A s) = (term290 A s).
Proof. exact (fun_ext (fun x : A => @lem5814830 A s x)). Qed.
Lemma lem5814832 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814833 {A : Type'} (s : A -> Prop) : (term153 A s) = (term291 A s).
Proof. exact (MK_COMB (@lem5814832 A) (@lem5814831 A s)). Qed.
Lemma lem5814834 {A : Type'} : (term154 A) = (term292 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5814833 A s)). Qed.
Lemma lem5814835 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5814836 {A : Type'} : (term8 A) = (term293 A).
Proof. exact (MK_COMB (@lem5814835 A) (@lem5814834 A)). Qed.
Lemma lem5814846 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5814847 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (@lem5814846 A P Q). Qed.
Lemma lem5814848 {A : Type'} (s : A -> Prop) (x : A) : (term296 A s x) = (term297 A s x).
Proof. exact (@lem5814847 A (term298 A s x) (term299 A s x)). Qed.
Lemma lem5814849 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term300 A s x y) = (term283 A s x y).
Proof. exact (eq_refl (term300 A s x y)). Qed.
Lemma lem5814850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5814851 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term301 A s x y) = (term285 A s x y).
Proof. exact (MK_COMB (@lem5814850) (@lem5814849 A s x y)). Qed.
Lemma lem5814852 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term302 A s x y) = (term280 A s x y).
Proof. exact (eq_refl (term302 A s x y)). Qed.
Lemma lem5814853 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term303 A s x y) = (term287 A s x y).
Proof. exact (MK_COMB (@lem5814851 A s x y) (@lem5814852 A s x y)). Qed.
Lemma lem5814854 {A : Type'} (s : A -> Prop) (x : A) : (term304 A s x) = (term288 A s x).
Proof. exact (fun_ext (fun y : A => @lem5814853 A s x y)). Qed.
Lemma lem5814855 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814856 {A : Type'} (s : A -> Prop) (x : A) : (term296 A s x) = (term289 A s x).
Proof. exact (MK_COMB (@lem5814855 A) (@lem5814854 A s x)). Qed.
Lemma lem5814857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5814858 {A : Type'} (s : A -> Prop) (x : A) : (term305 A s x) = (term306 A s x).
Proof. exact (MK_COMB (@lem5814857) (@lem5814856 A s x)). Qed.
Lemma lem5814859 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term300 A s x y) = (term283 A s x y).
Proof. exact (eq_refl (term300 A s x y)). Qed.
Lemma lem5814860 {A : Type'} (s : A -> Prop) (x : A) : (term307 A s x) = (term298 A s x).
Proof. exact (fun_ext (fun y : A => @lem5814859 A s x y)). Qed.
Lemma lem5814861 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814862 {A : Type'} (s : A -> Prop) (x : A) : (term308 A s x) = (term309 A s x).
Proof. exact (MK_COMB (@lem5814861 A) (@lem5814860 A s x)). Qed.
Lemma lem5814863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5814864 {A : Type'} (s : A -> Prop) (x : A) : (term310 A s x) = (term311 A s x).
Proof. exact (MK_COMB (@lem5814863) (@lem5814862 A s x)). Qed.
Lemma lem5814865 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term302 A s x y) = (term280 A s x y).
Proof. exact (eq_refl (term302 A s x y)). Qed.
Lemma lem5814866 {A : Type'} (s : A -> Prop) (x : A) : (term312 A s x) = (term299 A s x).
Proof. exact (fun_ext (fun y : A => @lem5814865 A s x y)). Qed.
Lemma lem5814867 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814868 {A : Type'} (s : A -> Prop) (x : A) : (term313 A s x) = (term314 A s x).
Proof. exact (MK_COMB (@lem5814867 A) (@lem5814866 A s x)). Qed.
Lemma lem5814869 {A : Type'} (s : A -> Prop) (x : A) : (term297 A s x) = (term315 A s x).
Proof. exact (MK_COMB (@lem5814864 A s x) (@lem5814868 A s x)). Qed.
Lemma lem5814870 {A : Type'} (s : A -> Prop) (x : A) : ((term296 A s x) = (term297 A s x)) = ((term289 A s x) = (term315 A s x)).
Proof. exact (MK_COMB (@lem5814858 A s x) (@lem5814869 A s x)). Qed.
Lemma lem5814871 {A : Type'} (s : A -> Prop) (x : A) : (term289 A s x) = (term315 A s x).
Proof. exact (EQ_MP (@lem5814870 A s x) (@lem5814848 A s x)). Qed.
Lemma lem5814968 {A : Type'} (s : A -> Prop) : (term290 A s) = (term316 A s).
Proof. exact (fun_ext (fun x : A => @lem5814871 A s x)). Qed.
Lemma lem5814969 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814970 {A : Type'} (s : A -> Prop) : (term291 A s) = (term317 A s).
Proof. exact (MK_COMB (@lem5814969 A) (@lem5814968 A s)). Qed.
Lemma lem5814972 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5814973 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (@lem5814972 A P Q). Qed.
Lemma lem5814974 {A : Type'} (s : A -> Prop) : (term318 A s) = (term319 A s).
Proof. exact (@lem5814973 A (term320 A s) (term321 A s)). Qed.
Lemma lem5814975 {A : Type'} (s : A -> Prop) (x : A) : (term322 A s x) = (term309 A s x).
Proof. exact (eq_refl (term322 A s x)). Qed.
Lemma lem5814976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5814977 {A : Type'} (s : A -> Prop) (x : A) : (term323 A s x) = (term311 A s x).
Proof. exact (MK_COMB (@lem5814976) (@lem5814975 A s x)). Qed.
Lemma lem5814978 {A : Type'} (s : A -> Prop) (x : A) : (term324 A s x) = (term314 A s x).
Proof. exact (eq_refl (term324 A s x)). Qed.
Lemma lem5814979 {A : Type'} (s : A -> Prop) (x : A) : (term325 A s x) = (term315 A s x).
Proof. exact (MK_COMB (@lem5814977 A s x) (@lem5814978 A s x)). Qed.
Lemma lem5814980 {A : Type'} (s : A -> Prop) : (term326 A s) = (term316 A s).
Proof. exact (fun_ext (fun x : A => @lem5814979 A s x)). Qed.
Lemma lem5814981 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814982 {A : Type'} (s : A -> Prop) : (term318 A s) = (term317 A s).
Proof. exact (MK_COMB (@lem5814981 A) (@lem5814980 A s)). Qed.
Lemma lem5814983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5814984 {A : Type'} (s : A -> Prop) : (term327 A s) = (term328 A s).
Proof. exact (MK_COMB (@lem5814983) (@lem5814982 A s)). Qed.
Lemma lem5814985 {A : Type'} (s : A -> Prop) (x : A) : (term322 A s x) = (term309 A s x).
Proof. exact (eq_refl (term322 A s x)). Qed.
Lemma lem5814986 {A : Type'} (s : A -> Prop) : (term329 A s) = (term320 A s).
Proof. exact (fun_ext (fun x : A => @lem5814985 A s x)). Qed.
Lemma lem5814987 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814988 {A : Type'} (s : A -> Prop) : (term330 A s) = (term331 A s).
Proof. exact (MK_COMB (@lem5814987 A) (@lem5814986 A s)). Qed.
Lemma lem5814989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5814990 {A : Type'} (s : A -> Prop) : (term332 A s) = (term333 A s).
Proof. exact (MK_COMB (@lem5814989) (@lem5814988 A s)). Qed.
Lemma lem5814991 {A : Type'} (s : A -> Prop) (x : A) : (term324 A s x) = (term314 A s x).
Proof. exact (eq_refl (term324 A s x)). Qed.
Lemma lem5814992 {A : Type'} (s : A -> Prop) : (term334 A s) = (term321 A s).
Proof. exact (fun_ext (fun x : A => @lem5814991 A s x)). Qed.
Lemma lem5814993 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5814994 {A : Type'} (s : A -> Prop) : (term335 A s) = (term336 A s).
Proof. exact (MK_COMB (@lem5814993 A) (@lem5814992 A s)). Qed.
Lemma lem5814995 {A : Type'} (s : A -> Prop) : (term319 A s) = (term337 A s).
Proof. exact (MK_COMB (@lem5814990 A s) (@lem5814994 A s)). Qed.
Lemma lem5814996 {A : Type'} (s : A -> Prop) : ((term318 A s) = (term319 A s)) = ((term317 A s) = (term337 A s)).
Proof. exact (MK_COMB (@lem5814984 A s) (@lem5814995 A s)). Qed.
Lemma lem5814997 {A : Type'} (s : A -> Prop) : (term317 A s) = (term337 A s).
Proof. exact (EQ_MP (@lem5814996 A s) (@lem5814974 A s)). Qed.
Lemma lem5815102 {A : Type'} (s : A -> Prop) : (term291 A s) = (term337 A s).
Proof. exact (TRANS (@lem5814970 A s) (@lem5814997 A s)). Qed.
Lemma lem5815103 {A : Type'} : (term292 A) = (term338 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5815102 A s)). Qed.
Lemma lem5815104 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5815105 {A : Type'} : (term293 A) = (term339 A).
Proof. exact (MK_COMB (@lem5815104 A) (@lem5815103 A)). Qed.
Lemma lem5815107 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5815108 {A : Type'} (P : type686 A) (Q : type686 A) : (term340 A P Q) = (term341 A P Q).
Proof. exact (@lem5815107 (A -> Prop) P Q). Qed.
Lemma lem5815109 {A : Type'} : (term342 A) = (term343 A).
Proof. exact (@lem5815108 A (term344 A) (term345 A)). Qed.
Lemma lem5815110 {A : Type'} (s : A -> Prop) : (term346 A s) = (term331 A s).
Proof. exact (eq_refl (term346 A s)). Qed.
Lemma lem5815111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5815112 {A : Type'} (s : A -> Prop) : (term347 A s) = (term333 A s).
Proof. exact (MK_COMB (@lem5815111) (@lem5815110 A s)). Qed.
Lemma lem5815113 {A : Type'} (s : A -> Prop) : (term348 A s) = (term336 A s).
Proof. exact (eq_refl (term348 A s)). Qed.
Lemma lem5815114 {A : Type'} (s : A -> Prop) : (term349 A s) = (term337 A s).
Proof. exact (MK_COMB (@lem5815112 A s) (@lem5815113 A s)). Qed.
Lemma lem5815115 {A : Type'} : (term350 A) = (term338 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5815114 A s)). Qed.
Lemma lem5815116 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5815117 {A : Type'} : (term342 A) = (term339 A).
Proof. exact (MK_COMB (@lem5815116 A) (@lem5815115 A)). Qed.
Lemma lem5815118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5815119 {A : Type'} : (term351 A) = (term352 A).
Proof. exact (MK_COMB (@lem5815118) (@lem5815117 A)). Qed.
Lemma lem5815120 {A : Type'} (s : A -> Prop) : (term346 A s) = (term331 A s).
Proof. exact (eq_refl (term346 A s)). Qed.
Lemma lem5815121 {A : Type'} : (term353 A) = (term344 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5815120 A s)). Qed.
Lemma lem5815122 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5815123 {A : Type'} : (term354 A) = (term355 A).
Proof. exact (MK_COMB (@lem5815122 A) (@lem5815121 A)). Qed.
Lemma lem5815124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5815125 {A : Type'} : (term356 A) = (term357 A).
Proof. exact (MK_COMB (@lem5815124) (@lem5815123 A)). Qed.
Lemma lem5815126 {A : Type'} (s : A -> Prop) : (term348 A s) = (term336 A s).
Proof. exact (eq_refl (term348 A s)). Qed.
Lemma lem5815127 {A : Type'} : (term358 A) = (term345 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5815126 A s)). Qed.
Lemma lem5815128 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5815129 {A : Type'} : (term359 A) = (term360 A).
Proof. exact (MK_COMB (@lem5815128 A) (@lem5815127 A)). Qed.
Lemma lem5815130 {A : Type'} : (term343 A) = (term361 A).
Proof. exact (MK_COMB (@lem5815125 A) (@lem5815129 A)). Qed.
Lemma lem5815131 {A : Type'} : ((term342 A) = (term343 A)) = ((term339 A) = (term361 A)).
Proof. exact (MK_COMB (@lem5815119 A) (@lem5815130 A)). Qed.
Lemma lem5815132 {A : Type'} : (term339 A) = (term361 A).
Proof. exact (EQ_MP (@lem5815131 A) (@lem5815109 A)). Qed.
Lemma lem5815247 {A : Type'} : (term293 A) = (term361 A).
Proof. exact (TRANS (@lem5815105 A) (@lem5815132 A)). Qed.
Lemma lem5815248 {A : Type'} : (term8 A) = (term361 A).
Proof. exact (TRANS (@lem5814836 A) (@lem5815247 A)). Qed.
Lemma lem5815249 {A : Type'} (h1 : term8 A) : term361 A.
Proof. exact (EQ_MP (@lem5815248 A) (@lem5813399 A h1)). Qed.
Lemma lem5815988 {A : Type'} (x : A) (s : A -> Prop) : ((term142 A s x) = (@FINITE A s)) = (term362 A x s).
Proof. exact (@lem17784 (term142 A s x) (@FINITE A s)). Qed.
Lemma lem5815989 {A : Type'} (s : A -> Prop) : (term143 A s) = (term363 A s).
Proof. exact (fun_ext (fun x : A => @lem5815988 A x s)). Qed.
Lemma lem5815990 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5815991 {A : Type'} (s : A -> Prop) : (term144 A s) = (term364 A s).
Proof. exact (MK_COMB (@lem5815990 A) (@lem5815989 A s)). Qed.
Lemma lem5815992 {A : Type'} : (term145 A) = (term365 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5815991 A s)). Qed.
Lemma lem5815993 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5815994 {A : Type'} : (term7 A) = (term366 A).
Proof. exact (MK_COMB (@lem5815993 A) (@lem5815992 A)). Qed.
Lemma lem5816000 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5816001 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (@lem5816000 A P Q). Qed.
Lemma lem5816002 {A : Type'} (s : A -> Prop) : (term367 A s) = (term368 A s).
Proof. exact (@lem5816001 A (term369 A s) (term370 A s)). Qed.
Lemma lem5816003 {A : Type'} (x : A) (s : A -> Prop) : (term371 A s x) = (term372 A x s).
Proof. exact (eq_refl (term371 A s x)). Qed.
Lemma lem5816004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5816005 {A : Type'} (x : A) (s : A -> Prop) : (term373 A s x) = (term374 A x s).
Proof. exact (MK_COMB (@lem5816004) (@lem5816003 A x s)). Qed.
Lemma lem5816006 {A : Type'} (x : A) (s : A -> Prop) : (term375 A s x) = (term376 A x s).
Proof. exact (eq_refl (term375 A s x)). Qed.
Lemma lem5816007 {A : Type'} (x : A) (s : A -> Prop) : (term377 A s x) = (term362 A x s).
Proof. exact (MK_COMB (@lem5816005 A x s) (@lem5816006 A x s)). Qed.
Lemma lem5816008 {A : Type'} (s : A -> Prop) : (term378 A s) = (term363 A s).
Proof. exact (fun_ext (fun x : A => @lem5816007 A x s)). Qed.
Lemma lem5816009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5816010 {A : Type'} (s : A -> Prop) : (term367 A s) = (term364 A s).
Proof. exact (MK_COMB (@lem5816009 A) (@lem5816008 A s)). Qed.
Lemma lem5816011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5816012 {A : Type'} (s : A -> Prop) : (term379 A s) = (term380 A s).
Proof. exact (MK_COMB (@lem5816011) (@lem5816010 A s)). Qed.
Lemma lem5816013 {A : Type'} (x : A) (s : A -> Prop) : (term371 A s x) = (term372 A x s).
Proof. exact (eq_refl (term371 A s x)). Qed.
Lemma lem5816014 {A : Type'} (s : A -> Prop) : (term381 A s) = (term369 A s).
Proof. exact (fun_ext (fun x : A => @lem5816013 A x s)). Qed.
Lemma lem5816015 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5816016 {A : Type'} (s : A -> Prop) : (term382 A s) = (term383 A s).
Proof. exact (MK_COMB (@lem5816015 A) (@lem5816014 A s)). Qed.
Lemma lem5816017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5816018 {A : Type'} (s : A -> Prop) : (term384 A s) = (term385 A s).
Proof. exact (MK_COMB (@lem5816017) (@lem5816016 A s)). Qed.
Lemma lem5816019 {A : Type'} (x : A) (s : A -> Prop) : (term375 A s x) = (term376 A x s).
Proof. exact (eq_refl (term375 A s x)). Qed.
Lemma lem5816020 {A : Type'} (s : A -> Prop) : (term386 A s) = (term370 A s).
Proof. exact (fun_ext (fun x : A => @lem5816019 A x s)). Qed.
Lemma lem5816021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5816022 {A : Type'} (s : A -> Prop) : (term387 A s) = (term388 A s).
Proof. exact (MK_COMB (@lem5816021 A) (@lem5816020 A s)). Qed.
Lemma lem5816023 {A : Type'} (s : A -> Prop) : (term368 A s) = (term389 A s).
Proof. exact (MK_COMB (@lem5816018 A s) (@lem5816022 A s)). Qed.
Lemma lem5816024 {A : Type'} (s : A -> Prop) : ((term367 A s) = (term368 A s)) = ((term364 A s) = (term389 A s)).
Proof. exact (MK_COMB (@lem5816012 A s) (@lem5816023 A s)). Qed.
Lemma lem5816025 {A : Type'} (s : A -> Prop) : (term364 A s) = (term389 A s).
Proof. exact (EQ_MP (@lem5816024 A s) (@lem5816002 A s)). Qed.
Lemma lem5816047 {A : Type'} (P : A -> Prop) (Q : Prop) : (term390 A P Q) = (term391 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem5816048 {A : Type'} (P : A -> Prop) (Q : Prop) : (term390 A P Q) = (term391 A P Q).
Proof. exact (@lem5816047 A P Q). Qed.
Lemma lem5816049 {A : Type'} (s : A -> Prop) : (term392 A s) = (term393 A s).
Proof. exact (@lem5816048 A (term394 A s) (term395 A s)). Qed.
Lemma lem5816050 {A : Type'} (s : A -> Prop) (x : A) : (term396 A s x) = (term142 A s x).
Proof. exact (eq_refl (term396 A s x)). Qed.
Lemma lem5816051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5816052 {A : Type'} (s : A -> Prop) (x : A) : (term397 A s x) = (term398 A s x).
Proof. exact (MK_COMB (@lem5816051) (@lem5816050 A s x)). Qed.
Lemma lem5816053 {A : Type'} (s : A -> Prop) : (term395 A s) = (term395 A s).
Proof. exact (eq_refl (term395 A s)). Qed.
Lemma lem5816054 {A : Type'} (x : A) (s : A -> Prop) : (term399 A x s) = (term372 A x s).
Proof. exact (MK_COMB (@lem5816052 A s x) (@lem5816053 A s)). Qed.
Lemma lem5816055 {A : Type'} (s : A -> Prop) : (term400 A s) = (term369 A s).
Proof. exact (fun_ext (fun x : A => @lem5816054 A x s)). Qed.
Lemma lem5816056 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5816057 {A : Type'} (s : A -> Prop) : (term392 A s) = (term383 A s).
Proof. exact (MK_COMB (@lem5816056 A) (@lem5816055 A s)). Qed.
Lemma lem5816058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5816059 {A : Type'} (s : A -> Prop) : (term401 A s) = (term402 A s).
Proof. exact (MK_COMB (@lem5816058) (@lem5816057 A s)). Qed.
Lemma lem5816060 {A : Type'} (s : A -> Prop) (x : A) : (term396 A s x) = (term142 A s x).
Proof. exact (eq_refl (term396 A s x)). Qed.
Lemma lem5816061 {A : Type'} (s : A -> Prop) : (term403 A s) = (term394 A s).
Proof. exact (fun_ext (fun x : A => @lem5816060 A s x)). Qed.
Lemma lem5816062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5816063 {A : Type'} (s : A -> Prop) : (term404 A s) = (term405 A s).
Proof. exact (MK_COMB (@lem5816062 A) (@lem5816061 A s)). Qed.
Lemma lem5816064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5816065 {A : Type'} (s : A -> Prop) : (term406 A s) = (term407 A s).
Proof. exact (MK_COMB (@lem5816064) (@lem5816063 A s)). Qed.
Lemma lem5816066 {A : Type'} (s : A -> Prop) : (term395 A s) = (term395 A s).
Proof. exact (eq_refl (term395 A s)). Qed.
Lemma lem5816067 {A : Type'} (s : A -> Prop) : (term393 A s) = (term408 A s).
Proof. exact (MK_COMB (@lem5816065 A s) (@lem5816066 A s)). Qed.
Lemma lem5816068 {A : Type'} (s : A -> Prop) : ((term392 A s) = (term393 A s)) = ((term383 A s) = (term408 A s)).
Proof. exact (MK_COMB (@lem5816059 A s) (@lem5816067 A s)). Qed.
Lemma lem5816069 {A : Type'} (s : A -> Prop) : (term383 A s) = (term408 A s).
Proof. exact (EQ_MP (@lem5816068 A s) (@lem5816049 A s)). Qed.
Lemma lem5816074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5816075 {A : Type'} (s : A -> Prop) : (term385 A s) = (term409 A s).
Proof. exact (MK_COMB (@lem5816074) (@lem5816069 A s)). Qed.
Lemma lem5816097 {A : Type'} (P : A -> Prop) (Q : Prop) : (term390 A P Q) = (term391 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem5816098 {A : Type'} (P : A -> Prop) (Q : Prop) : (term390 A P Q) = (term391 A P Q).
Proof. exact (@lem5816097 A P Q). Qed.
Lemma lem5816099 {A : Type'} (s : A -> Prop) : (term410 A s) = (term411 A s).
Proof. exact (@lem5816098 A (term412 A s) (@FINITE A s)). Qed.
Lemma lem5816100 {A : Type'} (s : A -> Prop) (x : A) : (term413 A s x) = (term414 A s x).
Proof. exact (eq_refl (term413 A s x)). Qed.
Lemma lem5816101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5816102 {A : Type'} (s : A -> Prop) (x : A) : (term415 A s x) = (term416 A s x).
Proof. exact (MK_COMB (@lem5816101) (@lem5816100 A s x)). Qed.
Lemma lem5816103 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem5816104 {A : Type'} (x : A) (s : A -> Prop) : (term417 A x s) = (term376 A x s).
Proof. exact (MK_COMB (@lem5816102 A s x) (@lem5816103 A s)). Qed.
Lemma lem5816105 {A : Type'} (s : A -> Prop) : (term418 A s) = (term370 A s).
Proof. exact (fun_ext (fun x : A => @lem5816104 A x s)). Qed.
Lemma lem5816106 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5816107 {A : Type'} (s : A -> Prop) : (term410 A s) = (term388 A s).
Proof. exact (MK_COMB (@lem5816106 A) (@lem5816105 A s)). Qed.
Lemma lem5816108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5816109 {A : Type'} (s : A -> Prop) : (term419 A s) = (term420 A s).
Proof. exact (MK_COMB (@lem5816108) (@lem5816107 A s)). Qed.
Lemma lem5816110 {A : Type'} (s : A -> Prop) (x : A) : (term413 A s x) = (term414 A s x).
Proof. exact (eq_refl (term413 A s x)). Qed.
Lemma lem5816111 {A : Type'} (s : A -> Prop) : (term421 A s) = (term412 A s).
Proof. exact (fun_ext (fun x : A => @lem5816110 A s x)). Qed.
Lemma lem5816112 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5816113 {A : Type'} (s : A -> Prop) : (term422 A s) = (term423 A s).
Proof. exact (MK_COMB (@lem5816112 A) (@lem5816111 A s)). Qed.
Lemma lem5816114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5816115 {A : Type'} (s : A -> Prop) : (term424 A s) = (term425 A s).
Proof. exact (MK_COMB (@lem5816114) (@lem5816113 A s)). Qed.
Lemma lem5816116 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem5816117 {A : Type'} (s : A -> Prop) : (term411 A s) = (term426 A s).
Proof. exact (MK_COMB (@lem5816115 A s) (@lem5816116 A s)). Qed.
Lemma lem5816118 {A : Type'} (s : A -> Prop) : ((term410 A s) = (term411 A s)) = ((term388 A s) = (term426 A s)).
Proof. exact (MK_COMB (@lem5816109 A s) (@lem5816117 A s)). Qed.
Lemma lem5816119 {A : Type'} (s : A -> Prop) : (term388 A s) = (term426 A s).
Proof. exact (EQ_MP (@lem5816118 A s) (@lem5816099 A s)). Qed.
Lemma lem5816124 {A : Type'} (s : A -> Prop) : (term389 A s) = (term427 A s).
Proof. exact (MK_COMB (@lem5816075 A s) (@lem5816119 A s)). Qed.
Lemma lem5816125 {A : Type'} (s : A -> Prop) : (term364 A s) = (term427 A s).
Proof. exact (TRANS (@lem5816025 A s) (@lem5816124 A s)). Qed.
Lemma lem5816126 {A : Type'} : (term365 A) = (term428 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5816125 A s)). Qed.
Lemma lem5816127 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5816128 {A : Type'} : (term366 A) = (term429 A).
Proof. exact (MK_COMB (@lem5816127 A) (@lem5816126 A)). Qed.
Lemma lem5816130 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5816131 {A : Type'} (P : type686 A) (Q : type686 A) : (term340 A P Q) = (term341 A P Q).
Proof. exact (@lem5816130 (A -> Prop) P Q). Qed.
Lemma lem5816132 {A : Type'} : (term430 A) = (term431 A).
Proof. exact (@lem5816131 A (term432 A) (term433 A)). Qed.
Lemma lem5816133 {A : Type'} (s : A -> Prop) : (term434 A s) = (term408 A s).
Proof. exact (eq_refl (term434 A s)). Qed.
Lemma lem5816134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5816135 {A : Type'} (s : A -> Prop) : (term435 A s) = (term409 A s).
Proof. exact (MK_COMB (@lem5816134) (@lem5816133 A s)). Qed.
Lemma lem5816136 {A : Type'} (s : A -> Prop) : (term436 A s) = (term426 A s).
Proof. exact (eq_refl (term436 A s)). Qed.
Lemma lem5816137 {A : Type'} (s : A -> Prop) : (term437 A s) = (term427 A s).
Proof. exact (MK_COMB (@lem5816135 A s) (@lem5816136 A s)). Qed.
Lemma lem5816138 {A : Type'} : (term438 A) = (term428 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5816137 A s)). Qed.
Lemma lem5816139 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5816140 {A : Type'} : (term430 A) = (term429 A).
Proof. exact (MK_COMB (@lem5816139 A) (@lem5816138 A)). Qed.
Lemma lem5816141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5816142 {A : Type'} : (term439 A) = (term440 A).
Proof. exact (MK_COMB (@lem5816141) (@lem5816140 A)). Qed.
Lemma lem5816143 {A : Type'} (s : A -> Prop) : (term434 A s) = (term408 A s).
Proof. exact (eq_refl (term434 A s)). Qed.
Lemma lem5816144 {A : Type'} : (term441 A) = (term432 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5816143 A s)). Qed.
Lemma lem5816145 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5816146 {A : Type'} : (term442 A) = (term443 A).
Proof. exact (MK_COMB (@lem5816145 A) (@lem5816144 A)). Qed.
Lemma lem5816147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5816148 {A : Type'} : (term444 A) = (term445 A).
Proof. exact (MK_COMB (@lem5816147) (@lem5816146 A)). Qed.
Lemma lem5816149 {A : Type'} (s : A -> Prop) : (term436 A s) = (term426 A s).
Proof. exact (eq_refl (term436 A s)). Qed.
Lemma lem5816150 {A : Type'} : (term446 A) = (term433 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5816149 A s)). Qed.
Lemma lem5816151 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5816152 {A : Type'} : (term447 A) = (term448 A).
Proof. exact (MK_COMB (@lem5816151 A) (@lem5816150 A)). Qed.
Lemma lem5816153 {A : Type'} : (term431 A) = (term449 A).
Proof. exact (MK_COMB (@lem5816148 A) (@lem5816152 A)). Qed.
Lemma lem5816154 {A : Type'} : ((term430 A) = (term431 A)) = ((term429 A) = (term449 A)).
Proof. exact (MK_COMB (@lem5816142 A) (@lem5816153 A)). Qed.
Lemma lem5816155 {A : Type'} : (term429 A) = (term449 A).
Proof. exact (EQ_MP (@lem5816154 A) (@lem5816132 A)). Qed.
Lemma lem5816246 {A : Type'} : (term366 A) = (term449 A).
Proof. exact (TRANS (@lem5816128 A) (@lem5816155 A)). Qed.
Lemma lem5816247 {A : Type'} : (term7 A) = (term449 A).
Proof. exact (TRANS (@lem5815994 A) (@lem5816246 A)). Qed.
Lemma lem5816248 {A : Type'} (h1 : term7 A) : term449 A.
Proof. exact (EQ_MP (@lem5816247 A) (@lem5813402 A h1)). Qed.
Lemma lem5817390 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)) = ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)).
Proof. exact (eq_refl ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op))). Qed.
Lemma lem5817391 {_120477 B : Type'} (op : type1400 B) : (term81 _120477 B op) = (term81 _120477 B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5817390 _120477 B f op)). Qed.
Lemma lem5817392 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5817393 {_120477 B : Type'} (op : type1400 B) : (term82 _120477 B op) = (term82 _120477 B op).
Proof. exact (MK_COMB (@lem5817392 _120477 B) (@lem5817391 _120477 B op)). Qed.
Lemma lem5817401 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term63 A B x op s f) = (term450 A B x op s f).
Proof. exact (@lem17265 (@FINITE A s) ((term56 A B op x s f) = (@iterate B A op s f))). Qed.
Lemma lem5817403 {A : Type'} (x : A) (s : A -> Prop) : (term275 A x s) = (term275 A x s).
Proof. exact (eq_refl (term275 A x s)). Qed.
Lemma lem5817404 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term451 A B x op s f) = (term452 A B x op s f).
Proof. exact (MK_COMB (@lem5817403 A x s) (@lem5817401 A B x op s f)). Qed.
Lemma lem5817412 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term59 A B x op s f) = (term453 A B x op s f).
Proof. exact (@lem17265 (@FINITE A s) ((term56 A B op x s f) = (term52 A B x op s f))). Qed.
Lemma lem5817414 {A : Type'} (x : A) (s : A -> Prop) : (term454 A x s) = (term454 A x s).
Proof. exact (eq_refl (term454 A x s)). Qed.
Lemma lem5817415 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term455 A B x op s f) = (term456 A B x op s f).
Proof. exact (MK_COMB (@lem5817414 A x s) (@lem5817412 A B x op s f)). Qed.
Lemma lem5817416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5817417 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term457 A B x op s f) = (term458 A B x op s f).
Proof. exact (MK_COMB (@lem5817416) (@lem5817404 A B x op s f)). Qed.
Lemma lem5817418 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term68 A B x op s f) = (term459 A B x op s f).
Proof. exact (MK_COMB (@lem5817417 A B x op s f) (@lem5817415 A B x op s f)). Qed.
Lemma lem5817419 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term70 A B x op f) = (term460 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5817418 A B x op s f)). Qed.
Lemma lem5817420 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5817421 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term72 A B x op f) = (term461 A B x op f).
Proof. exact (MK_COMB (@lem5817420 A) (@lem5817419 A B x op f)). Qed.
Lemma lem5817422 {A B : Type'} (op : type1400 B) (f : A -> B) : (term74 A B op f) = (term462 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5817421 A B x op f)). Qed.
Lemma lem5817423 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5817424 {A B : Type'} (op : type1400 B) (f : A -> B) : (term76 A B op f) = (term463 A B op f).
Proof. exact (MK_COMB (@lem5817423 A) (@lem5817422 A B op f)). Qed.
Lemma lem5817425 {A B : Type'} (op : type1400 B) : (term78 A B op) = (term464 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5817424 A B op f)). Qed.
Lemma lem5817426 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5817427 {A B : Type'} (op : type1400 B) : (term80 A B op) = (term465 A B op).
Proof. exact (MK_COMB (@lem5817426 A B) (@lem5817425 A B op)). Qed.
Lemma lem5817428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5817429 {_120477 B : Type'} (op : type1400 B) : (term83 _120477 B op) = (term83 _120477 B op).
Proof. exact (MK_COMB (@lem5817428) (@lem5817393 _120477 B op)). Qed.
Lemma lem5817430 {_120477 A B : Type'} (op : type1400 B) : (term94 _120477 A B op) = (term466 _120477 A B op).
Proof. exact (MK_COMB (@lem5817429 _120477 B op) (@lem5817427 A B op)). Qed.
Lemma lem5817432 {B : Type'} (op : type1400 B) : (term467 B op) = (term467 B op).
Proof. exact (eq_refl (term467 B op)). Qed.
Lemma lem5817433 {_120477 A B : Type'} (op : type1400 B) : (term468 _120477 A B op) = (term469 _120477 A B op).
Proof. exact (MK_COMB (@lem5817432 B op) (@lem5817430 _120477 A B op)). Qed.
Lemma lem5817434 {_120477 A B : Type'} (op : type1400 B) : (term96 _120477 A B op) = (term468 _120477 A B op).
Proof. exact (@lem17265 (@monoidal B op) (term94 _120477 A B op)). Qed.
Lemma lem5817435 {_120477 A B : Type'} (op : type1400 B) : (term96 _120477 A B op) = (term469 _120477 A B op).
Proof. exact (TRANS (@lem5817434 _120477 A B op) (@lem5817433 _120477 A B op)). Qed.
Lemma lem5817436 {_120477 A B : Type'} : (term98 _120477 A B) = (term470 _120477 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5817435 _120477 A B op)). Qed.
Lemma lem5817437 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5817438 {_120477 A B : Type'} : (term99 _120477 A B) = (term471 _120477 A B).
Proof. exact (MK_COMB (@lem5817437 B) (@lem5817436 _120477 A B)). Qed.
Lemma lem5817500 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5817501 {A : Type'} (P : type686 A) (Q : type686 A) : (term340 A P Q) = (term341 A P Q).
Proof. exact (@lem5817500 (A -> Prop) P Q). Qed.
Lemma lem5817502 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term472 A B x op f) = (term473 A B x op f).
Proof. exact (@lem5817501 A (term474 A B x op f) (term475 A B x op f)). Qed.
Lemma lem5817503 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term476 A B x op f s) = (term452 A B x op s f).
Proof. exact (eq_refl (term476 A B x op f s)). Qed.
Lemma lem5817504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5817505 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term477 A B x op f s) = (term458 A B x op s f).
Proof. exact (MK_COMB (@lem5817504) (@lem5817503 A B x op s f)). Qed.
Lemma lem5817506 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term478 A B x op f s) = (term456 A B x op s f).
Proof. exact (eq_refl (term478 A B x op f s)). Qed.
Lemma lem5817507 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term479 A B x op f s) = (term459 A B x op s f).
Proof. exact (MK_COMB (@lem5817505 A B x op s f) (@lem5817506 A B x op s f)). Qed.
Lemma lem5817508 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term480 A B x op f) = (term460 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5817507 A B x op s f)). Qed.
Lemma lem5817509 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5817510 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term472 A B x op f) = (term461 A B x op f).
Proof. exact (MK_COMB (@lem5817509 A) (@lem5817508 A B x op f)). Qed.
Lemma lem5817511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5817512 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term481 A B x op f) = (term482 A B x op f).
Proof. exact (MK_COMB (@lem5817511) (@lem5817510 A B x op f)). Qed.
Lemma lem5817513 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term476 A B x op f s) = (term452 A B x op s f).
Proof. exact (eq_refl (term476 A B x op f s)). Qed.
Lemma lem5817514 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term483 A B x op f) = (term474 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5817513 A B x op s f)). Qed.
Lemma lem5817515 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5817516 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term484 A B x op f) = (term485 A B x op f).
Proof. exact (MK_COMB (@lem5817515 A) (@lem5817514 A B x op f)). Qed.
Lemma lem5817517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5817518 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term486 A B x op f) = (term487 A B x op f).
Proof. exact (MK_COMB (@lem5817517) (@lem5817516 A B x op f)). Qed.
Lemma lem5817519 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term478 A B x op f s) = (term456 A B x op s f).
Proof. exact (eq_refl (term478 A B x op f s)). Qed.
Lemma lem5817520 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term488 A B x op f) = (term475 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5817519 A B x op s f)). Qed.
Lemma lem5817521 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5817522 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term489 A B x op f) = (term490 A B x op f).
Proof. exact (MK_COMB (@lem5817521 A) (@lem5817520 A B x op f)). Qed.
Lemma lem5817523 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term473 A B x op f) = (term491 A B x op f).
Proof. exact (MK_COMB (@lem5817518 A B x op f) (@lem5817522 A B x op f)). Qed.
Lemma lem5817524 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : ((term472 A B x op f) = (term473 A B x op f)) = ((term461 A B x op f) = (term491 A B x op f)).
Proof. exact (MK_COMB (@lem5817512 A B x op f) (@lem5817523 A B x op f)). Qed.
Lemma lem5817525 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term461 A B x op f) = (term491 A B x op f).
Proof. exact (EQ_MP (@lem5817524 A B x op f) (@lem5817502 A B x op f)). Qed.
Lemma lem5817622 {A B : Type'} (op : type1400 B) (f : A -> B) : (term462 A B op f) = (term492 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5817525 A B x op f)). Qed.
Lemma lem5817623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5817624 {A B : Type'} (op : type1400 B) (f : A -> B) : (term463 A B op f) = (term493 A B op f).
Proof. exact (MK_COMB (@lem5817623 A) (@lem5817622 A B op f)). Qed.
Lemma lem5817626 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5817627 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (@lem5817626 A P Q). Qed.
Lemma lem5817628 {A B : Type'} (op : type1400 B) (f : A -> B) : (term494 A B op f) = (term495 A B op f).
Proof. exact (@lem5817627 A (term496 A B op f) (term497 A B op f)). Qed.
Lemma lem5817629 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term498 A B op f x) = (term485 A B x op f).
Proof. exact (eq_refl (term498 A B op f x)). Qed.
Lemma lem5817630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5817631 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term499 A B op f x) = (term487 A B x op f).
Proof. exact (MK_COMB (@lem5817630) (@lem5817629 A B x op f)). Qed.
Lemma lem5817632 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term500 A B op f x) = (term490 A B x op f).
Proof. exact (eq_refl (term500 A B op f x)). Qed.
Lemma lem5817633 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term501 A B op f x) = (term491 A B x op f).
Proof. exact (MK_COMB (@lem5817631 A B x op f) (@lem5817632 A B x op f)). Qed.
Lemma lem5817634 {A B : Type'} (op : type1400 B) (f : A -> B) : (term502 A B op f) = (term492 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5817633 A B x op f)). Qed.
Lemma lem5817635 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5817636 {A B : Type'} (op : type1400 B) (f : A -> B) : (term494 A B op f) = (term493 A B op f).
Proof. exact (MK_COMB (@lem5817635 A) (@lem5817634 A B op f)). Qed.
Lemma lem5817637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5817638 {A B : Type'} (op : type1400 B) (f : A -> B) : (term503 A B op f) = (term504 A B op f).
Proof. exact (MK_COMB (@lem5817637) (@lem5817636 A B op f)). Qed.
Lemma lem5817639 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term498 A B op f x) = (term485 A B x op f).
Proof. exact (eq_refl (term498 A B op f x)). Qed.
Lemma lem5817640 {A B : Type'} (op : type1400 B) (f : A -> B) : (term505 A B op f) = (term496 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5817639 A B x op f)). Qed.
Lemma lem5817641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5817642 {A B : Type'} (op : type1400 B) (f : A -> B) : (term506 A B op f) = (term507 A B op f).
Proof. exact (MK_COMB (@lem5817641 A) (@lem5817640 A B op f)). Qed.
Lemma lem5817643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5817644 {A B : Type'} (op : type1400 B) (f : A -> B) : (term508 A B op f) = (term509 A B op f).
Proof. exact (MK_COMB (@lem5817643) (@lem5817642 A B op f)). Qed.
Lemma lem5817645 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term500 A B op f x) = (term490 A B x op f).
Proof. exact (eq_refl (term500 A B op f x)). Qed.
Lemma lem5817646 {A B : Type'} (op : type1400 B) (f : A -> B) : (term510 A B op f) = (term497 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5817645 A B x op f)). Qed.
Lemma lem5817647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5817648 {A B : Type'} (op : type1400 B) (f : A -> B) : (term511 A B op f) = (term512 A B op f).
Proof. exact (MK_COMB (@lem5817647 A) (@lem5817646 A B op f)). Qed.
Lemma lem5817649 {A B : Type'} (op : type1400 B) (f : A -> B) : (term495 A B op f) = (term513 A B op f).
Proof. exact (MK_COMB (@lem5817644 A B op f) (@lem5817648 A B op f)). Qed.
Lemma lem5817650 {A B : Type'} (op : type1400 B) (f : A -> B) : ((term494 A B op f) = (term495 A B op f)) = ((term493 A B op f) = (term513 A B op f)).
Proof. exact (MK_COMB (@lem5817638 A B op f) (@lem5817649 A B op f)). Qed.
Lemma lem5817651 {A B : Type'} (op : type1400 B) (f : A -> B) : (term493 A B op f) = (term513 A B op f).
Proof. exact (EQ_MP (@lem5817650 A B op f) (@lem5817628 A B op f)). Qed.
Lemma lem5817756 {A B : Type'} (op : type1400 B) (f : A -> B) : (term463 A B op f) = (term513 A B op f).
Proof. exact (TRANS (@lem5817624 A B op f) (@lem5817651 A B op f)). Qed.
Lemma lem5817757 {A B : Type'} (op : type1400 B) : (term464 A B op) = (term514 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5817756 A B op f)). Qed.
Lemma lem5817758 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5817759 {A B : Type'} (op : type1400 B) : (term465 A B op) = (term515 A B op).
Proof. exact (MK_COMB (@lem5817758 A B) (@lem5817757 A B op)). Qed.
Lemma lem5817761 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5817762 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term516 A B P Q) = (term517 A B P Q).
Proof. exact (@lem5817761 (A -> B) P Q). Qed.
Lemma lem5817763 {A B : Type'} (op : type1400 B) : (term518 A B op) = (term519 A B op).
Proof. exact (@lem5817762 A B (term520 A B op) (term521 A B op)). Qed.
Lemma lem5817764 {A B : Type'} (op : type1400 B) (f : A -> B) : (term522 A B op f) = (term507 A B op f).
Proof. exact (eq_refl (term522 A B op f)). Qed.
Lemma lem5817765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5817766 {A B : Type'} (op : type1400 B) (f : A -> B) : (term523 A B op f) = (term509 A B op f).
Proof. exact (MK_COMB (@lem5817765) (@lem5817764 A B op f)). Qed.
Lemma lem5817767 {A B : Type'} (op : type1400 B) (f : A -> B) : (term524 A B op f) = (term512 A B op f).
Proof. exact (eq_refl (term524 A B op f)). Qed.
Lemma lem5817768 {A B : Type'} (op : type1400 B) (f : A -> B) : (term525 A B op f) = (term513 A B op f).
Proof. exact (MK_COMB (@lem5817766 A B op f) (@lem5817767 A B op f)). Qed.
Lemma lem5817769 {A B : Type'} (op : type1400 B) : (term526 A B op) = (term514 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5817768 A B op f)). Qed.
Lemma lem5817770 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5817771 {A B : Type'} (op : type1400 B) : (term518 A B op) = (term515 A B op).
Proof. exact (MK_COMB (@lem5817770 A B) (@lem5817769 A B op)). Qed.
Lemma lem5817772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5817773 {A B : Type'} (op : type1400 B) : (term527 A B op) = (term528 A B op).
Proof. exact (MK_COMB (@lem5817772) (@lem5817771 A B op)). Qed.
Lemma lem5817774 {A B : Type'} (op : type1400 B) (f : A -> B) : (term522 A B op f) = (term507 A B op f).
Proof. exact (eq_refl (term522 A B op f)). Qed.
Lemma lem5817775 {A B : Type'} (op : type1400 B) : (term529 A B op) = (term520 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5817774 A B op f)). Qed.
Lemma lem5817776 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5817777 {A B : Type'} (op : type1400 B) : (term530 A B op) = (term531 A B op).
Proof. exact (MK_COMB (@lem5817776 A B) (@lem5817775 A B op)). Qed.
Lemma lem5817778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5817779 {A B : Type'} (op : type1400 B) : (term532 A B op) = (term533 A B op).
Proof. exact (MK_COMB (@lem5817778) (@lem5817777 A B op)). Qed.
Lemma lem5817780 {A B : Type'} (op : type1400 B) (f : A -> B) : (term524 A B op f) = (term512 A B op f).
Proof. exact (eq_refl (term524 A B op f)). Qed.
Lemma lem5817781 {A B : Type'} (op : type1400 B) : (term534 A B op) = (term521 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5817780 A B op f)). Qed.
Lemma lem5817782 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5817783 {A B : Type'} (op : type1400 B) : (term535 A B op) = (term536 A B op).
Proof. exact (MK_COMB (@lem5817782 A B) (@lem5817781 A B op)). Qed.
Lemma lem5817784 {A B : Type'} (op : type1400 B) : (term519 A B op) = (term537 A B op).
Proof. exact (MK_COMB (@lem5817779 A B op) (@lem5817783 A B op)). Qed.
Lemma lem5817785 {A B : Type'} (op : type1400 B) : ((term518 A B op) = (term519 A B op)) = ((term515 A B op) = (term537 A B op)).
Proof. exact (MK_COMB (@lem5817773 A B op) (@lem5817784 A B op)). Qed.
Lemma lem5817786 {A B : Type'} (op : type1400 B) : (term515 A B op) = (term537 A B op).
Proof. exact (EQ_MP (@lem5817785 A B op) (@lem5817763 A B op)). Qed.
Lemma lem5817899 {A B : Type'} (op : type1400 B) : (term465 A B op) = (term537 A B op).
Proof. exact (TRANS (@lem5817759 A B op) (@lem5817786 A B op)). Qed.
Lemma lem5817900 {_120477 B : Type'} (op : type1400 B) : (term83 _120477 B op) = (term83 _120477 B op).
Proof. exact (eq_refl (term83 _120477 B op)). Qed.
Lemma lem5817901 {_120477 A B : Type'} (op : type1400 B) : (term466 _120477 A B op) = (term538 _120477 A B op).
Proof. exact (MK_COMB (@lem5817900 _120477 B op) (@lem5817899 A B op)). Qed.
Lemma lem5817902 {B : Type'} (op : type1400 B) : (term467 B op) = (term467 B op).
Proof. exact (eq_refl (term467 B op)). Qed.
Lemma lem5817903 {_120477 A B : Type'} (op : type1400 B) : (term469 _120477 A B op) = (term539 _120477 A B op).
Proof. exact (MK_COMB (@lem5817902 B op) (@lem5817901 _120477 A B op)). Qed.
Lemma lem5817904 {_120477 A B : Type'} : (term470 _120477 A B) = (term540 _120477 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5817903 _120477 A B op)). Qed.
Lemma lem5817905 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5817956 {_120477 A B : Type'} : (term471 _120477 A B) = (term541 _120477 A B).
Proof. exact (MK_COMB (@lem5817905 B) (@lem5817904 _120477 A B)). Qed.
Lemma lem5817957 {_120477 A B : Type'} : (term99 _120477 A B) = (term541 _120477 A B).
Proof. exact (TRANS (@lem5817438 _120477 A B) (@lem5817956 _120477 A B)). Qed.
Lemma lem5817958 {_120477 A B : Type'} (h1 : term99 _120477 A B) : term541 _120477 A B.
Proof. exact (EQ_MP (@lem5817957 _120477 A B) (@lem5813405 _120477 A B h1)). Qed.
Lemma lem5818529 {A B : Type'} (op : type1400 B) (h1 : term265 A B op) : term265 A B op.
Proof. exact (h1). Qed.
Lemma lem5818530 {A B : Type'} (op : type1400 B) (f : A -> B) (h1 : term263 A B op f) : term263 A B op f.
Proof. exact (h1). Qed.
Lemma lem5818531 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term261 A B op s f) : term261 A B op s f.
Proof. exact (h1). Qed.
Lemma lem5818532 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term258 A B a op s f.
Proof. exact (h1). Qed.
Lemma lem5818665 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem5818674 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5818675 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem5818674 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem5818676 {A : Type'} (s : A -> Prop) : (@DELETE A s) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s).
Proof. exact (@lem5818675 A (@DELETE A) s). Qed.
Lemma lem5818677 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5818678 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s x).
Proof. exact (MK_COMB (@lem5818676 A s) (@lem5818677 A x)). Qed.
Lemma lem5818680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5818681 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5818680 A (A -> Prop) f x). Qed.
Lemma lem5818682 {A : Type'} (s : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s x) = (term542 A s x).
Proof. exact (@lem5818681 A (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s) x). Qed.
Lemma lem5818684 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (term542 A s x).
Proof. exact (TRANS (@lem5818678 A s x) (@lem5818682 A s x)). Qed.
Lemma lem5818685 {A : Type'} (x : A) : (@INSERT A x) = (@INSERT A x).
Proof. exact (eq_refl (@INSERT A x)). Qed.
Lemma lem5818686 {A : Type'} (s : A -> Prop) (x : A) : (term269 A s x) = (term543 A s x).
Proof. exact (MK_COMB (@lem5818685 A x) (@lem5818684 A s x)). Qed.
Lemma lem5818688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5818689 {A : Type'} (f : type1363 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5818688 A (type672 A) f x). Qed.
Lemma lem5818690 {A : Type'} (x : A) : (@INSERT A x) = (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x).
Proof. exact (@lem5818689 A (@INSERT A) x). Qed.
Lemma lem5818691 {A : Type'} (s : A -> Prop) (x : A) : (term542 A s x) = (term542 A s x).
Proof. exact (eq_refl (term542 A s x)). Qed.
Lemma lem5818692 {A : Type'} (s : A -> Prop) (x : A) : (term543 A s x) = (term544 A s x).
Proof. exact (MK_COMB (@lem5818690 A x) (@lem5818691 A s x)). Qed.
Lemma lem5818694 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5818695 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5818694 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5818696 {A : Type'} (s : A -> Prop) (x : A) : (term544 A s x) = (term545 A s x).
Proof. exact (@lem5818695 A (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x) (term542 A s x)). Qed.
Lemma lem5818697 {A : Type'} (s : A -> Prop) (x : A) : (term543 A s x) = (term545 A s x).
Proof. exact (TRANS (@lem5818692 A s x) (@lem5818696 A s x)). Qed.
Lemma lem5818698 {A : Type'} (s : A -> Prop) (x : A) : (term269 A s x) = (term545 A s x).
Proof. exact (TRANS (@lem5818686 A s x) (@lem5818697 A s x)). Qed.
Lemma lem5818699 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5818700 {A : Type'} (s : A -> Prop) (x : A) : (term546 A s x) = (term547 A s x).
Proof. exact (MK_COMB (@lem5818665 A) (@lem5818698 A s x)). Qed.
Lemma lem5818701 {A : Type'} (x : A) (s : A -> Prop) : ((term269 A s x) = s) = ((term545 A s x) = s).
Proof. exact (MK_COMB (@lem5818700 A s x) (@lem5818699 A s)). Qed.
Lemma lem5818702 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5818709 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5818710 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5818709 A (type686 A) f x). Qed.
Lemma lem5818711 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5818710 A (@IN A) x). Qed.
Lemma lem5818712 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5818713 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5818711 A x) (@lem5818712 A s)). Qed.
Lemma lem5818715 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5818716 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5818715 (A -> Prop) Prop f x). Qed.
Lemma lem5818717 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term548 A x s).
Proof. exact (@lem5818716 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5818719 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term548 A x s).
Proof. exact (TRANS (@lem5818713 A x s) (@lem5818717 A x s)). Qed.
Lemma lem5818720 {A : Type'} (x : A) (s : A -> Prop) : (term549 A x s) = (term550 A x s).
Proof. exact (MK_COMB (@lem5818702) (@lem5818719 A x s)). Qed.
Lemma lem5818721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5818722 {A : Type'} (x : A) (s : A -> Prop) : (term275 A x s) = (term551 A x s).
Proof. exact (MK_COMB (@lem5818721) (@lem5818720 A x s)). Qed.
Lemma lem5818723 {A : Type'} (x : A) (s : A -> Prop) : (term268 A x s) = (term552 A x s).
Proof. exact (MK_COMB (@lem5818722 A x s) (@lem5818701 A x s)). Qed.
Lemma lem5818724 {A : Type'} (x : A) : (term270 A x) = (term553 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5818723 A x s)). Qed.
Lemma lem5818725 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5818726 {A : Type'} (x : A) : (term271 A x) = (term554 A x).
Proof. exact (MK_COMB (@lem5818725 A) (@lem5818724 A x)). Qed.
Lemma lem5818727 {A : Type'} : (term272 A) = (term555 A).
Proof. exact (fun_ext (fun x : A => @lem5818726 A x)). Qed.
Lemma lem5818728 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5818729 {A : Type'} : (term273 A) = (term556 A).
Proof. exact (MK_COMB (@lem5818728 A) (@lem5818727 A)). Qed.
Lemma lem5818730 {A : Type'} (h1 : term9 A) : term556 A.
Proof. exact (EQ_MP (@lem5818729 A) (@lem5813832 A h1)). Qed.
Lemma lem5819103 {A : Type'} (x : A) (y : A) : (term279 A x y) = (term279 A x y).
Proof. exact (eq_refl (term279 A x y)). Qed.
Lemma lem5819110 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819111 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5819110 A (type686 A) f x). Qed.
Lemma lem5819112 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5819111 A (@IN A) x). Qed.
Lemma lem5819113 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5819114 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5819112 A x) (@lem5819113 A s)). Qed.
Lemma lem5819116 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819117 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5819116 (A -> Prop) Prop f x). Qed.
Lemma lem5819118 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term548 A x s).
Proof. exact (@lem5819117 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5819120 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term548 A x s).
Proof. exact (TRANS (@lem5819114 A x s) (@lem5819118 A x s)). Qed.
Lemma lem5819121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5819122 {A : Type'} (x : A) (s : A -> Prop) : (term557 A x s) = (term558 A x s).
Proof. exact (MK_COMB (@lem5819121) (@lem5819120 A x s)). Qed.
Lemma lem5819123 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term149 A s x y) = (term559 A s x y).
Proof. exact (MK_COMB (@lem5819122 A x s) (@lem5819103 A x y)). Qed.
Lemma lem5819124 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5819133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819134 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem5819133 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem5819135 {A : Type'} (s : A -> Prop) : (@DELETE A s) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s).
Proof. exact (@lem5819134 A (@DELETE A) s). Qed.
Lemma lem5819136 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5819137 {A : Type'} (s : A -> Prop) (y : A) : (@DELETE A s y) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s y).
Proof. exact (MK_COMB (@lem5819135 A s) (@lem5819136 A y)). Qed.
Lemma lem5819139 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819140 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5819139 A (A -> Prop) f x). Qed.
Lemma lem5819141 {A : Type'} (s : A -> Prop) (y : A) : (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s y) = (term542 A s y).
Proof. exact (@lem5819140 A (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s) y). Qed.
Lemma lem5819143 {A : Type'} (s : A -> Prop) (y : A) : (@DELETE A s y) = (term542 A s y).
Proof. exact (TRANS (@lem5819137 A s y) (@lem5819141 A s y)). Qed.
Lemma lem5819144 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5819145 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term148 A x s y) = (term560 A x s y).
Proof. exact (MK_COMB (@lem5819144 A x) (@lem5819143 A s y)). Qed.
Lemma lem5819147 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819148 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5819147 A (type686 A) f x). Qed.
Lemma lem5819149 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5819148 A (@IN A) x). Qed.
Lemma lem5819150 {A : Type'} (s : A -> Prop) (y : A) : (term542 A s y) = (term542 A s y).
Proof. exact (eq_refl (term542 A s y)). Qed.
Lemma lem5819151 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term560 A x s y) = (term561 A x s y).
Proof. exact (MK_COMB (@lem5819149 A x) (@lem5819150 A s y)). Qed.
Lemma lem5819153 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819154 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5819153 (A -> Prop) Prop f x). Qed.
Lemma lem5819155 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term561 A x s y) = (term562 A x s y).
Proof. exact (@lem5819154 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (term542 A s y)). Qed.
Lemma lem5819156 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term560 A x s y) = (term562 A x s y).
Proof. exact (TRANS (@lem5819151 A x s y) (@lem5819155 A x s y)). Qed.
Lemma lem5819157 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term148 A x s y) = (term562 A x s y).
Proof. exact (TRANS (@lem5819145 A x s y) (@lem5819156 A x s y)). Qed.
Lemma lem5819158 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term563 A x s y) = (term564 A x s y).
Proof. exact (MK_COMB (@lem5819124) (@lem5819157 A x s y)). Qed.
Lemma lem5819159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5819160 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term565 A x s y) = (term566 A x s y).
Proof. exact (MK_COMB (@lem5819159) (@lem5819158 A x s y)). Qed.
Lemma lem5819161 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term280 A s x y) = (term567 A s x y).
Proof. exact (MK_COMB (@lem5819160 A x s y) (@lem5819123 A s x y)). Qed.
Lemma lem5819162 {A : Type'} (s : A -> Prop) (x : A) : (term299 A s x) = (term568 A s x).
Proof. exact (fun_ext (fun y : A => @lem5819161 A s x y)). Qed.
Lemma lem5819163 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5819164 {A : Type'} (s : A -> Prop) (x : A) : (term314 A s x) = (term569 A s x).
Proof. exact (MK_COMB (@lem5819163 A) (@lem5819162 A s x)). Qed.
Lemma lem5819165 {A : Type'} (s : A -> Prop) : (term321 A s) = (term570 A s).
Proof. exact (fun_ext (fun x : A => @lem5819164 A s x)). Qed.
Lemma lem5819166 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5819167 {A : Type'} (s : A -> Prop) : (term336 A s) = (term571 A s).
Proof. exact (MK_COMB (@lem5819166 A) (@lem5819165 A s)). Qed.
Lemma lem5819168 {A : Type'} : (term345 A) = (term572 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5819167 A s)). Qed.
Lemma lem5819169 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5819170 {A : Type'} : (term360 A) = (term573 A).
Proof. exact (MK_COMB (@lem5819169 A) (@lem5819168 A)). Qed.
Lemma lem5819175 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5819176 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5819183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819184 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5819183 A (type686 A) f x). Qed.
Lemma lem5819185 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5819184 A (@IN A) x). Qed.
Lemma lem5819186 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5819187 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5819185 A x) (@lem5819186 A s)). Qed.
Lemma lem5819189 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819190 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5819189 (A -> Prop) Prop f x). Qed.
Lemma lem5819191 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term548 A x s).
Proof. exact (@lem5819190 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5819193 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term548 A x s).
Proof. exact (TRANS (@lem5819187 A x s) (@lem5819191 A x s)). Qed.
Lemma lem5819194 {A : Type'} (x : A) (s : A -> Prop) : (term549 A x s) = (term550 A x s).
Proof. exact (MK_COMB (@lem5819176) (@lem5819193 A x s)). Qed.
Lemma lem5819195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5819196 {A : Type'} (x : A) (s : A -> Prop) : (term275 A x s) = (term551 A x s).
Proof. exact (MK_COMB (@lem5819195) (@lem5819194 A x s)). Qed.
Lemma lem5819197 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term277 A s x y) = (term574 A s x y).
Proof. exact (MK_COMB (@lem5819196 A x s) (@lem5819175 A x y)). Qed.
Lemma lem5819206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819207 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem5819206 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem5819208 {A : Type'} (s : A -> Prop) : (@DELETE A s) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s).
Proof. exact (@lem5819207 A (@DELETE A) s). Qed.
Lemma lem5819209 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5819210 {A : Type'} (s : A -> Prop) (y : A) : (@DELETE A s y) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s y).
Proof. exact (MK_COMB (@lem5819208 A s) (@lem5819209 A y)). Qed.
Lemma lem5819212 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819213 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5819212 A (A -> Prop) f x). Qed.
Lemma lem5819214 {A : Type'} (s : A -> Prop) (y : A) : (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s y) = (term542 A s y).
Proof. exact (@lem5819213 A (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s) y). Qed.
Lemma lem5819216 {A : Type'} (s : A -> Prop) (y : A) : (@DELETE A s y) = (term542 A s y).
Proof. exact (TRANS (@lem5819210 A s y) (@lem5819214 A s y)). Qed.
Lemma lem5819217 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5819218 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term148 A x s y) = (term560 A x s y).
Proof. exact (MK_COMB (@lem5819217 A x) (@lem5819216 A s y)). Qed.
Lemma lem5819220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819221 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5819220 A (type686 A) f x). Qed.
Lemma lem5819222 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5819221 A (@IN A) x). Qed.
Lemma lem5819223 {A : Type'} (s : A -> Prop) (y : A) : (term542 A s y) = (term542 A s y).
Proof. exact (eq_refl (term542 A s y)). Qed.
Lemma lem5819224 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term560 A x s y) = (term561 A x s y).
Proof. exact (MK_COMB (@lem5819222 A x) (@lem5819223 A s y)). Qed.
Lemma lem5819226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819227 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5819226 (A -> Prop) Prop f x). Qed.
Lemma lem5819228 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term561 A x s y) = (term562 A x s y).
Proof. exact (@lem5819227 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (term542 A s y)). Qed.
Lemma lem5819229 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term560 A x s y) = (term562 A x s y).
Proof. exact (TRANS (@lem5819224 A x s y) (@lem5819228 A x s y)). Qed.
Lemma lem5819230 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term148 A x s y) = (term562 A x s y).
Proof. exact (TRANS (@lem5819218 A x s y) (@lem5819229 A x s y)). Qed.
Lemma lem5819231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5819232 {A : Type'} (x : A) (s : A -> Prop) (y : A) : (term281 A x s y) = (term575 A x s y).
Proof. exact (MK_COMB (@lem5819231) (@lem5819230 A x s y)). Qed.
Lemma lem5819233 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term283 A s x y) = (term576 A s x y).
Proof. exact (MK_COMB (@lem5819232 A x s y) (@lem5819197 A s x y)). Qed.
Lemma lem5819234 {A : Type'} (s : A -> Prop) (x : A) : (term298 A s x) = (term577 A s x).
Proof. exact (fun_ext (fun y : A => @lem5819233 A s x y)). Qed.
Lemma lem5819235 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5819236 {A : Type'} (s : A -> Prop) (x : A) : (term309 A s x) = (term578 A s x).
Proof. exact (MK_COMB (@lem5819235 A) (@lem5819234 A s x)). Qed.
Lemma lem5819237 {A : Type'} (s : A -> Prop) : (term320 A s) = (term579 A s).
Proof. exact (fun_ext (fun x : A => @lem5819236 A s x)). Qed.
Lemma lem5819238 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5819239 {A : Type'} (s : A -> Prop) : (term331 A s) = (term580 A s).
Proof. exact (MK_COMB (@lem5819238 A) (@lem5819237 A s)). Qed.
Lemma lem5819240 {A : Type'} : (term344 A) = (term581 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5819239 A s)). Qed.
Lemma lem5819241 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5819242 {A : Type'} : (term355 A) = (term582 A).
Proof. exact (MK_COMB (@lem5819241 A) (@lem5819240 A)). Qed.
Lemma lem5819243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5819244 {A : Type'} : (term357 A) = (term583 A).
Proof. exact (MK_COMB (@lem5819243) (@lem5819242 A)). Qed.
Lemma lem5819245 {A : Type'} : (term361 A) = (term584 A).
Proof. exact (MK_COMB (@lem5819244 A) (@lem5819170 A)). Qed.
Lemma lem5819246 {A : Type'} (h1 : term8 A) : term584 A.
Proof. exact (EQ_MP (@lem5819245 A) (@lem5815249 A h1)). Qed.
Lemma lem5819491 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819492 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5819491 (A -> Prop) Prop f x). Qed.
Lemma lem5819494 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5819492 A (@FINITE A) s). Qed.
Lemma lem5819495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5819496 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5819503 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819504 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem5819503 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem5819505 {A : Type'} (s : A -> Prop) : (@DELETE A s) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s).
Proof. exact (@lem5819504 A (@DELETE A) s). Qed.
Lemma lem5819506 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5819507 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s x).
Proof. exact (MK_COMB (@lem5819505 A s) (@lem5819506 A x)). Qed.
Lemma lem5819509 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819510 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5819509 A (A -> Prop) f x). Qed.
Lemma lem5819511 {A : Type'} (s : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s x) = (term542 A s x).
Proof. exact (@lem5819510 A (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s) x). Qed.
Lemma lem5819513 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (term542 A s x).
Proof. exact (TRANS (@lem5819507 A s x) (@lem5819511 A s x)). Qed.
Lemma lem5819514 {A : Type'} (s : A -> Prop) (x : A) : (term142 A s x) = (term585 A s x).
Proof. exact (MK_COMB (@lem5819496 A) (@lem5819513 A s x)). Qed.
Lemma lem5819516 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819517 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5819516 (A -> Prop) Prop f x). Qed.
Lemma lem5819518 {A : Type'} (s : A -> Prop) (x : A) : (term585 A s x) = (term586 A s x).
Proof. exact (@lem5819517 A (@FINITE A) (term542 A s x)). Qed.
Lemma lem5819519 {A : Type'} (s : A -> Prop) (x : A) : (term142 A s x) = (term586 A s x).
Proof. exact (TRANS (@lem5819514 A s x) (@lem5819518 A s x)). Qed.
Lemma lem5819520 {A : Type'} (s : A -> Prop) (x : A) : (term414 A s x) = (term587 A s x).
Proof. exact (MK_COMB (@lem5819495) (@lem5819519 A s x)). Qed.
Lemma lem5819521 {A : Type'} (s : A -> Prop) : (term412 A s) = (term588 A s).
Proof. exact (fun_ext (fun x : A => @lem5819520 A s x)). Qed.
Lemma lem5819522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5819523 {A : Type'} (s : A -> Prop) : (term423 A s) = (term589 A s).
Proof. exact (MK_COMB (@lem5819522 A) (@lem5819521 A s)). Qed.
Lemma lem5819524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5819525 {A : Type'} (s : A -> Prop) : (term425 A s) = (term590 A s).
Proof. exact (MK_COMB (@lem5819524) (@lem5819523 A s)). Qed.
Lemma lem5819526 {A : Type'} (s : A -> Prop) : (term426 A s) = (term591 A s).
Proof. exact (MK_COMB (@lem5819525 A s) (@lem5819494 A s)). Qed.
Lemma lem5819527 {A : Type'} : (term433 A) = (term592 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5819526 A s)). Qed.
Lemma lem5819528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5819529 {A : Type'} : (term448 A) = (term593 A).
Proof. exact (MK_COMB (@lem5819528 A) (@lem5819527 A)). Qed.
Lemma lem5819530 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5819535 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819536 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5819535 (A -> Prop) Prop f x). Qed.
Lemma lem5819538 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5819536 A (@FINITE A) s). Qed.
Lemma lem5819539 {A : Type'} (s : A -> Prop) : (term395 A s) = (term594 A s).
Proof. exact (MK_COMB (@lem5819530) (@lem5819538 A s)). Qed.
Lemma lem5819540 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5819547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819548 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem5819547 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem5819549 {A : Type'} (s : A -> Prop) : (@DELETE A s) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s).
Proof. exact (@lem5819548 A (@DELETE A) s). Qed.
Lemma lem5819550 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5819551 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s x).
Proof. exact (MK_COMB (@lem5819549 A s) (@lem5819550 A x)). Qed.
Lemma lem5819553 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819554 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5819553 A (A -> Prop) f x). Qed.
Lemma lem5819555 {A : Type'} (s : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s x) = (term542 A s x).
Proof. exact (@lem5819554 A (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s) x). Qed.
Lemma lem5819557 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (term542 A s x).
Proof. exact (TRANS (@lem5819551 A s x) (@lem5819555 A s x)). Qed.
Lemma lem5819558 {A : Type'} (s : A -> Prop) (x : A) : (term142 A s x) = (term585 A s x).
Proof. exact (MK_COMB (@lem5819540 A) (@lem5819557 A s x)). Qed.
Lemma lem5819560 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5819561 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5819560 (A -> Prop) Prop f x). Qed.
Lemma lem5819562 {A : Type'} (s : A -> Prop) (x : A) : (term585 A s x) = (term586 A s x).
Proof. exact (@lem5819561 A (@FINITE A) (term542 A s x)). Qed.
Lemma lem5819563 {A : Type'} (s : A -> Prop) (x : A) : (term142 A s x) = (term586 A s x).
Proof. exact (TRANS (@lem5819558 A s x) (@lem5819562 A s x)). Qed.
Lemma lem5819564 {A : Type'} (s : A -> Prop) : (term394 A s) = (term595 A s).
Proof. exact (fun_ext (fun x : A => @lem5819563 A s x)). Qed.
Lemma lem5819565 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5819566 {A : Type'} (s : A -> Prop) : (term405 A s) = (term596 A s).
Proof. exact (MK_COMB (@lem5819565 A) (@lem5819564 A s)). Qed.
Lemma lem5819567 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5819568 {A : Type'} (s : A -> Prop) : (term407 A s) = (term597 A s).
Proof. exact (MK_COMB (@lem5819567) (@lem5819566 A s)). Qed.
Lemma lem5819569 {A : Type'} (s : A -> Prop) : (term408 A s) = (term598 A s).
Proof. exact (MK_COMB (@lem5819568 A s) (@lem5819539 A s)). Qed.
Lemma lem5819570 {A : Type'} : (term432 A) = (term599 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5819569 A s)). Qed.
Lemma lem5819571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5819572 {A : Type'} : (term443 A) = (term600 A).
Proof. exact (MK_COMB (@lem5819571 A) (@lem5819570 A)). Qed.
Lemma lem5819573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5819574 {A : Type'} : (term445 A) = (term601 A).
Proof. exact (MK_COMB (@lem5819573) (@lem5819572 A)). Qed.
Lemma lem5819575 {A : Type'} : (term449 A) = (term602 A).
Proof. exact (MK_COMB (@lem5819574 A) (@lem5819529 A)). Qed.
Lemma lem5819576 {A : Type'} (h1 : term7 A) : term602 A.
Proof. exact (EQ_MP (@lem5819575 A) (@lem5816248 A h1)). Qed.
Lemma lem5820203 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5820212 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820213 {A : Type'} (f : type1363 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5820212 A (type672 A) f x). Qed.
Lemma lem5820214 {A : Type'} (x : A) : (@INSERT A x) = (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x).
Proof. exact (@lem5820213 A (@INSERT A) x). Qed.
Lemma lem5820215 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5820216 {A : Type'} (x : A) (s : A -> Prop) : (@INSERT A x s) = (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x s).
Proof. exact (MK_COMB (@lem5820214 A x) (@lem5820215 A s)). Qed.
Lemma lem5820218 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820219 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5820218 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5820220 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x s) = (term603 A x s).
Proof. exact (@lem5820219 A (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x) s). Qed.
Lemma lem5820222 {A : Type'} (x : A) (s : A -> Prop) : (@INSERT A x s) = (term603 A x s).
Proof. exact (TRANS (@lem5820216 A x s) (@lem5820220 A x s)). Qed.
Lemma lem5820223 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820224 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5820225 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) : (term604 A B op x s) = (term605 A B op x s).
Proof. exact (MK_COMB (@lem5820224 A B op) (@lem5820222 A x s)). Qed.
Lemma lem5820226 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term56 A B op x s f) = (term606 A B op x s f).
Proof. exact (MK_COMB (@lem5820225 A B op x s) (@lem5820223 A B f)). Qed.
Lemma lem5820228 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820229 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820228 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5820230 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5820229 A B (@iterate B A) op). Qed.
Lemma lem5820231 {A : Type'} (x : A) (s : A -> Prop) : (term603 A x s) = (term603 A x s).
Proof. exact (eq_refl (term603 A x s)). Qed.
Lemma lem5820232 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) : (term605 A B op x s) = (term607 A B op x s).
Proof. exact (MK_COMB (@lem5820230 A B op) (@lem5820231 A x s)). Qed.
Lemma lem5820234 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820235 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820234 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5820236 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) : (term607 A B op x s) = (term608 A B op x s).
Proof. exact (@lem5820235 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) (term603 A x s)). Qed.
Lemma lem5820237 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) : (term605 A B op x s) = (term608 A B op x s).
Proof. exact (TRANS (@lem5820232 A B op x s) (@lem5820236 A B op x s)). Qed.
Lemma lem5820238 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820239 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term606 A B op x s f) = (term609 A B op x s f).
Proof. exact (MK_COMB (@lem5820237 A B op x s) (@lem5820238 A B f)). Qed.
Lemma lem5820241 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820242 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5820241 (A -> B) B f x). Qed.
Lemma lem5820243 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term609 A B op x s f) = (term610 A B op x s f).
Proof. exact (@lem5820242 A B (term608 A B op x s) f). Qed.
Lemma lem5820244 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term606 A B op x s f) = (term610 A B op x s f).
Proof. exact (TRANS (@lem5820239 A B op x s f) (@lem5820243 A B op x s f)). Qed.
Lemma lem5820245 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term56 A B op x s f) = (term610 A B op x s f).
Proof. exact (TRANS (@lem5820226 A B op x s f) (@lem5820244 A B op x s f)). Qed.
Lemma lem5820246 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5820251 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820253 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5820251 A B f x). Qed.
Lemma lem5820262 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820263 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820262 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5820264 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5820263 A B (@iterate B A) op). Qed.
Lemma lem5820265 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5820266 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s).
Proof. exact (MK_COMB (@lem5820264 A B op) (@lem5820265 A s)). Qed.
Lemma lem5820268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820269 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820268 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5820270 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s) = (term611 A B op s).
Proof. exact (@lem5820269 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) s). Qed.
Lemma lem5820271 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (term611 A B op s).
Proof. exact (TRANS (@lem5820266 A B op s) (@lem5820270 A B op s)). Qed.
Lemma lem5820272 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820273 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term612 A B op s f).
Proof. exact (MK_COMB (@lem5820271 A B op s) (@lem5820272 A B f)). Qed.
Lemma lem5820275 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820276 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5820275 (A -> B) B f x). Qed.
Lemma lem5820277 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term612 A B op s f) = (term613 A B op s f).
Proof. exact (@lem5820276 A B (term611 A B op s) f). Qed.
Lemma lem5820279 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term613 A B op s f).
Proof. exact (TRANS (@lem5820273 A B op s f) (@lem5820277 A B op s f)). Qed.
Lemma lem5820280 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term614 A B op f x) = (term615 A B op f x).
Proof. exact (MK_COMB (@lem5820246 B op) (@lem5820253 A B f x)). Qed.
Lemma lem5820281 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term52 A B x op s f) = (term616 A B x op s f).
Proof. exact (MK_COMB (@lem5820280 A B op f x) (@lem5820279 A B op s f)). Qed.
Lemma lem5820283 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820284 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5820283 B (B -> B) f x). Qed.
Lemma lem5820285 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term615 A B op f x) = (term617 A B op f x).
Proof. exact (@lem5820284 B op (@I (A -> B) f x)). Qed.
Lemma lem5820286 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term613 A B op s f) = (term613 A B op s f).
Proof. exact (eq_refl (term613 A B op s f)). Qed.
Lemma lem5820287 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term616 A B x op s f) = (term618 A B x op s f).
Proof. exact (MK_COMB (@lem5820285 A B op f x) (@lem5820286 A B op s f)). Qed.
Lemma lem5820289 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820290 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5820289 B B f x). Qed.
Lemma lem5820291 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term618 A B x op s f) = (term619 A B x op s f).
Proof. exact (@lem5820290 B (term617 A B op f x) (term613 A B op s f)). Qed.
Lemma lem5820292 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term616 A B x op s f) = (term619 A B x op s f).
Proof. exact (TRANS (@lem5820287 A B x op s f) (@lem5820291 A B x op s f)). Qed.
Lemma lem5820293 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term52 A B x op s f) = (term619 A B x op s f).
Proof. exact (TRANS (@lem5820281 A B x op s f) (@lem5820292 A B x op s f)). Qed.
Lemma lem5820294 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term55 A B op x s f) = (term620 A B op x s f).
Proof. exact (MK_COMB (@lem5820203 B) (@lem5820245 A B op x s f)). Qed.
Lemma lem5820295 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term56 A B op x s f) = (term52 A B x op s f)) = ((term610 A B op x s f) = (term619 A B x op s f)).
Proof. exact (MK_COMB (@lem5820294 A B op x s f) (@lem5820293 A B x op s f)). Qed.
Lemma lem5820296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5820301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820302 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5820301 (A -> Prop) Prop f x). Qed.
Lemma lem5820304 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5820302 A (@FINITE A) s). Qed.
Lemma lem5820305 {A : Type'} (s : A -> Prop) : (term395 A s) = (term594 A s).
Proof. exact (MK_COMB (@lem5820296) (@lem5820304 A s)). Qed.
Lemma lem5820306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5820307 {A : Type'} (s : A -> Prop) : (term621 A s) = (term622 A s).
Proof. exact (MK_COMB (@lem5820306) (@lem5820305 A s)). Qed.
Lemma lem5820308 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term453 A B x op s f) = (term623 A B x op s f).
Proof. exact (MK_COMB (@lem5820307 A s) (@lem5820295 A B x op s f)). Qed.
Lemma lem5820315 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820316 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5820315 A (type686 A) f x). Qed.
Lemma lem5820317 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5820316 A (@IN A) x). Qed.
Lemma lem5820318 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5820319 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5820317 A x) (@lem5820318 A s)). Qed.
Lemma lem5820321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820322 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5820321 (A -> Prop) Prop f x). Qed.
Lemma lem5820323 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term548 A x s).
Proof. exact (@lem5820322 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5820325 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term548 A x s).
Proof. exact (TRANS (@lem5820319 A x s) (@lem5820323 A x s)). Qed.
Lemma lem5820326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5820327 {A : Type'} (x : A) (s : A -> Prop) : (term454 A x s) = (term624 A x s).
Proof. exact (MK_COMB (@lem5820326) (@lem5820325 A x s)). Qed.
Lemma lem5820328 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term456 A B x op s f) = (term625 A B x op s f).
Proof. exact (MK_COMB (@lem5820327 A x s) (@lem5820308 A B x op s f)). Qed.
Lemma lem5820329 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term475 A B x op f) = (term626 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5820328 A B x op s f)). Qed.
Lemma lem5820330 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5820331 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term490 A B x op f) = (term627 A B x op f).
Proof. exact (MK_COMB (@lem5820330 A) (@lem5820329 A B x op f)). Qed.
Lemma lem5820332 {A B : Type'} (op : type1400 B) (f : A -> B) : (term497 A B op f) = (term628 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5820331 A B x op f)). Qed.
Lemma lem5820333 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5820334 {A B : Type'} (op : type1400 B) (f : A -> B) : (term512 A B op f) = (term629 A B op f).
Proof. exact (MK_COMB (@lem5820333 A) (@lem5820332 A B op f)). Qed.
Lemma lem5820335 {A B : Type'} (op : type1400 B) : (term521 A B op) = (term630 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5820334 A B op f)). Qed.
Lemma lem5820336 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5820337 {A B : Type'} (op : type1400 B) : (term536 A B op) = (term631 A B op).
Proof. exact (MK_COMB (@lem5820336 A B) (@lem5820335 A B op)). Qed.
Lemma lem5820338 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5820347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820348 {A : Type'} (f : type1363 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5820347 A (type672 A) f x). Qed.
Lemma lem5820349 {A : Type'} (x : A) : (@INSERT A x) = (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x).
Proof. exact (@lem5820348 A (@INSERT A) x). Qed.
Lemma lem5820350 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5820351 {A : Type'} (x : A) (s : A -> Prop) : (@INSERT A x s) = (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x s).
Proof. exact (MK_COMB (@lem5820349 A x) (@lem5820350 A s)). Qed.
Lemma lem5820353 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820354 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5820353 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5820355 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x s) = (term603 A x s).
Proof. exact (@lem5820354 A (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) x) s). Qed.
Lemma lem5820357 {A : Type'} (x : A) (s : A -> Prop) : (@INSERT A x s) = (term603 A x s).
Proof. exact (TRANS (@lem5820351 A x s) (@lem5820355 A x s)). Qed.
Lemma lem5820358 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820359 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5820360 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) : (term604 A B op x s) = (term605 A B op x s).
Proof. exact (MK_COMB (@lem5820359 A B op) (@lem5820357 A x s)). Qed.
Lemma lem5820361 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term56 A B op x s f) = (term606 A B op x s f).
Proof. exact (MK_COMB (@lem5820360 A B op x s) (@lem5820358 A B f)). Qed.
Lemma lem5820363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820364 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820363 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5820365 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5820364 A B (@iterate B A) op). Qed.
Lemma lem5820366 {A : Type'} (x : A) (s : A -> Prop) : (term603 A x s) = (term603 A x s).
Proof. exact (eq_refl (term603 A x s)). Qed.
Lemma lem5820367 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) : (term605 A B op x s) = (term607 A B op x s).
Proof. exact (MK_COMB (@lem5820365 A B op) (@lem5820366 A x s)). Qed.
Lemma lem5820369 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820370 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820369 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5820371 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) : (term607 A B op x s) = (term608 A B op x s).
Proof. exact (@lem5820370 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) (term603 A x s)). Qed.
Lemma lem5820372 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) : (term605 A B op x s) = (term608 A B op x s).
Proof. exact (TRANS (@lem5820367 A B op x s) (@lem5820371 A B op x s)). Qed.
Lemma lem5820373 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820374 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term606 A B op x s f) = (term609 A B op x s f).
Proof. exact (MK_COMB (@lem5820372 A B op x s) (@lem5820373 A B f)). Qed.
Lemma lem5820376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820377 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5820376 (A -> B) B f x). Qed.
Lemma lem5820378 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term609 A B op x s f) = (term610 A B op x s f).
Proof. exact (@lem5820377 A B (term608 A B op x s) f). Qed.
Lemma lem5820379 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term606 A B op x s f) = (term610 A B op x s f).
Proof. exact (TRANS (@lem5820374 A B op x s f) (@lem5820378 A B op x s f)). Qed.
Lemma lem5820380 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term56 A B op x s f) = (term610 A B op x s f).
Proof. exact (TRANS (@lem5820361 A B op x s f) (@lem5820379 A B op x s f)). Qed.
Lemma lem5820389 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820390 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820389 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5820391 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5820390 A B (@iterate B A) op). Qed.
Lemma lem5820392 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5820393 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s).
Proof. exact (MK_COMB (@lem5820391 A B op) (@lem5820392 A s)). Qed.
Lemma lem5820395 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820396 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820395 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5820397 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s) = (term611 A B op s).
Proof. exact (@lem5820396 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) s). Qed.
Lemma lem5820398 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (term611 A B op s).
Proof. exact (TRANS (@lem5820393 A B op s) (@lem5820397 A B op s)). Qed.
Lemma lem5820399 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820400 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term612 A B op s f).
Proof. exact (MK_COMB (@lem5820398 A B op s) (@lem5820399 A B f)). Qed.
Lemma lem5820402 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820403 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5820402 (A -> B) B f x). Qed.
Lemma lem5820404 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term612 A B op s f) = (term613 A B op s f).
Proof. exact (@lem5820403 A B (term611 A B op s) f). Qed.
Lemma lem5820406 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term613 A B op s f).
Proof. exact (TRANS (@lem5820400 A B op s f) (@lem5820404 A B op s f)). Qed.
Lemma lem5820407 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term55 A B op x s f) = (term620 A B op x s f).
Proof. exact (MK_COMB (@lem5820338 B) (@lem5820380 A B op x s f)). Qed.
Lemma lem5820408 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term56 A B op x s f) = (@iterate B A op s f)) = ((term610 A B op x s f) = (term613 A B op s f)).
Proof. exact (MK_COMB (@lem5820407 A B op x s f) (@lem5820406 A B op s f)). Qed.
Lemma lem5820409 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5820414 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820415 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5820414 (A -> Prop) Prop f x). Qed.
Lemma lem5820417 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5820415 A (@FINITE A) s). Qed.
Lemma lem5820418 {A : Type'} (s : A -> Prop) : (term395 A s) = (term594 A s).
Proof. exact (MK_COMB (@lem5820409) (@lem5820417 A s)). Qed.
Lemma lem5820419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5820420 {A : Type'} (s : A -> Prop) : (term621 A s) = (term622 A s).
Proof. exact (MK_COMB (@lem5820419) (@lem5820418 A s)). Qed.
Lemma lem5820421 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term450 A B x op s f) = (term632 A B x op s f).
Proof. exact (MK_COMB (@lem5820420 A s) (@lem5820408 A B x op s f)). Qed.
Lemma lem5820422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5820429 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820430 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5820429 A (type686 A) f x). Qed.
Lemma lem5820431 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5820430 A (@IN A) x). Qed.
Lemma lem5820432 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5820433 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5820431 A x) (@lem5820432 A s)). Qed.
Lemma lem5820435 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820436 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5820435 (A -> Prop) Prop f x). Qed.
Lemma lem5820437 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term548 A x s).
Proof. exact (@lem5820436 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5820439 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term548 A x s).
Proof. exact (TRANS (@lem5820433 A x s) (@lem5820437 A x s)). Qed.
Lemma lem5820440 {A : Type'} (x : A) (s : A -> Prop) : (term549 A x s) = (term550 A x s).
Proof. exact (MK_COMB (@lem5820422) (@lem5820439 A x s)). Qed.
Lemma lem5820441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5820442 {A : Type'} (x : A) (s : A -> Prop) : (term275 A x s) = (term551 A x s).
Proof. exact (MK_COMB (@lem5820441) (@lem5820440 A x s)). Qed.
Lemma lem5820443 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term452 A B x op s f) = (term633 A B x op s f).
Proof. exact (MK_COMB (@lem5820442 A x s) (@lem5820421 A B x op s f)). Qed.
Lemma lem5820444 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term474 A B x op f) = (term634 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5820443 A B x op s f)). Qed.
Lemma lem5820445 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5820446 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term485 A B x op f) = (term635 A B x op f).
Proof. exact (MK_COMB (@lem5820445 A) (@lem5820444 A B x op f)). Qed.
Lemma lem5820447 {A B : Type'} (op : type1400 B) (f : A -> B) : (term496 A B op f) = (term636 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5820446 A B x op f)). Qed.
Lemma lem5820448 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5820449 {A B : Type'} (op : type1400 B) (f : A -> B) : (term507 A B op f) = (term637 A B op f).
Proof. exact (MK_COMB (@lem5820448 A) (@lem5820447 A B op f)). Qed.
Lemma lem5820450 {A B : Type'} (op : type1400 B) : (term520 A B op) = (term638 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5820449 A B op f)). Qed.
Lemma lem5820451 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5820452 {A B : Type'} (op : type1400 B) : (term531 A B op) = (term639 A B op).
Proof. exact (MK_COMB (@lem5820451 A B) (@lem5820450 A B op)). Qed.
Lemma lem5820453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5820454 {A B : Type'} (op : type1400 B) : (term533 A B op) = (term640 A B op).
Proof. exact (MK_COMB (@lem5820453) (@lem5820452 A B op)). Qed.
Lemma lem5820455 {A B : Type'} (op : type1400 B) : (term537 A B op) = (term641 A B op).
Proof. exact (MK_COMB (@lem5820454 A B op) (@lem5820337 A B op)). Qed.
Lemma lem5820456 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5820465 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820466 {_120477 B : Type'} (f : type750 _120477 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (_120477 -> Prop) -> (_120477 -> B) -> B) f x).
Proof. exact (@lem5820465 (type1400 B) (type632 _120477 B) f x). Qed.
Lemma lem5820467 {_120477 B : Type'} (op : type1400 B) : (@iterate B _120477 op) = (@I ((B -> B -> B) -> (_120477 -> Prop) -> (_120477 -> B) -> B) (@iterate B _120477) op).
Proof. exact (@lem5820466 _120477 B (@iterate B _120477) op). Qed.
Lemma lem5820468 {_120477 : Type'} : (@EMPTY _120477) = (@EMPTY _120477).
Proof. exact (eq_refl (@EMPTY _120477)). Qed.
Lemma lem5820469 {_120477 B : Type'} (op : type1400 B) : (@iterate B _120477 op (@EMPTY _120477)) = (@I ((B -> B -> B) -> (_120477 -> Prop) -> (_120477 -> B) -> B) (@iterate B _120477) op (@EMPTY _120477)).
Proof. exact (MK_COMB (@lem5820467 _120477 B op) (@lem5820468 _120477)). Qed.
Lemma lem5820471 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820472 {_120477 B : Type'} (f : type632 _120477 B) (x : _120477 -> Prop) : (f x) = (@I ((_120477 -> Prop) -> (_120477 -> B) -> B) f x).
Proof. exact (@lem5820471 (_120477 -> Prop) (type570 _120477 B) f x). Qed.
Lemma lem5820473 {_120477 B : Type'} (op : type1400 B) : (@I ((B -> B -> B) -> (_120477 -> Prop) -> (_120477 -> B) -> B) (@iterate B _120477) op (@EMPTY _120477)) = (term642 _120477 B op).
Proof. exact (@lem5820472 _120477 B (@I ((B -> B -> B) -> (_120477 -> Prop) -> (_120477 -> B) -> B) (@iterate B _120477) op) (@EMPTY _120477)). Qed.
Lemma lem5820474 {_120477 B : Type'} (op : type1400 B) : (@iterate B _120477 op (@EMPTY _120477)) = (term642 _120477 B op).
Proof. exact (TRANS (@lem5820469 _120477 B op) (@lem5820473 _120477 B op)). Qed.
Lemma lem5820475 {_120477 B : Type'} (f : _120477 -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820476 {_120477 B : Type'} (op : type1400 B) (f : _120477 -> B) : (@iterate B _120477 op (@EMPTY _120477) f) = (term643 _120477 B op f).
Proof. exact (MK_COMB (@lem5820474 _120477 B op) (@lem5820475 _120477 B f)). Qed.
Lemma lem5820478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820479 {_120477 B : Type'} (f : type570 _120477 B) (x : _120477 -> B) : (f x) = (@I ((_120477 -> B) -> B) f x).
Proof. exact (@lem5820478 (_120477 -> B) B f x). Qed.
Lemma lem5820480 {_120477 B : Type'} (op : type1400 B) (f : _120477 -> B) : (term643 _120477 B op f) = (term644 _120477 B op f).
Proof. exact (@lem5820479 _120477 B (term642 _120477 B op) f). Qed.
Lemma lem5820482 {_120477 B : Type'} (op : type1400 B) (f : _120477 -> B) : (@iterate B _120477 op (@EMPTY _120477) f) = (term644 _120477 B op f).
Proof. exact (TRANS (@lem5820476 _120477 B op f) (@lem5820480 _120477 B op f)). Qed.
Lemma lem5820487 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820488 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5820487 (type1400 B) B f x). Qed.
Lemma lem5820490 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5820488 B (@neutral B) op). Qed.
Lemma lem5820491 {_120477 B : Type'} (op : type1400 B) (f : _120477 -> B) : (term645 _120477 B op f) = (term646 _120477 B op f).
Proof. exact (MK_COMB (@lem5820456 B) (@lem5820482 _120477 B op f)). Qed.
Lemma lem5820492 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : ((@iterate B _120477 op (@EMPTY _120477) f) = (@neutral B op)) = ((term644 _120477 B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem5820491 _120477 B op f) (@lem5820490 B op)). Qed.
Lemma lem5820493 {_120477 B : Type'} (op : type1400 B) : (term81 _120477 B op) = (term647 _120477 B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5820492 _120477 B f op)). Qed.
Lemma lem5820494 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5820495 {_120477 B : Type'} (op : type1400 B) : (term82 _120477 B op) = (term648 _120477 B op).
Proof. exact (MK_COMB (@lem5820494 _120477 B) (@lem5820493 _120477 B op)). Qed.
Lemma lem5820496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5820497 {_120477 B : Type'} (op : type1400 B) : (term83 _120477 B op) = (term649 _120477 B op).
Proof. exact (MK_COMB (@lem5820496) (@lem5820495 _120477 B op)). Qed.
Lemma lem5820498 {_120477 A B : Type'} (op : type1400 B) : (term538 _120477 A B op) = (term650 _120477 A B op).
Proof. exact (MK_COMB (@lem5820497 _120477 B op) (@lem5820455 A B op)). Qed.
Lemma lem5820499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5820504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820505 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem5820504 (type1400 B) Prop f x). Qed.
Lemma lem5820507 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5820505 B (@monoidal B) op). Qed.
Lemma lem5820508 {B : Type'} (op : type1400 B) : (term651 B op) = (term652 B op).
Proof. exact (MK_COMB (@lem5820499) (@lem5820507 B op)). Qed.
Lemma lem5820509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5820510 {B : Type'} (op : type1400 B) : (term467 B op) = (term653 B op).
Proof. exact (MK_COMB (@lem5820509) (@lem5820508 B op)). Qed.
Lemma lem5820511 {_120477 A B : Type'} (op : type1400 B) : (term539 _120477 A B op) = (term654 _120477 A B op).
Proof. exact (MK_COMB (@lem5820510 B op) (@lem5820498 _120477 A B op)). Qed.
Lemma lem5820512 {_120477 A B : Type'} : (term540 _120477 A B) = (term655 _120477 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5820511 _120477 A B op)). Qed.
Lemma lem5820513 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5820514 {_120477 A B : Type'} : (term541 _120477 A B) = (term656 _120477 A B).
Proof. exact (MK_COMB (@lem5820513 B) (@lem5820512 _120477 A B)). Qed.
Lemma lem5820515 {_120477 A B : Type'} (h1 : term99 _120477 A B) : term656 _120477 A B.
Proof. exact (EQ_MP (@lem5820514 _120477 A B) (@lem5817958 _120477 A B h1)). Qed.
Lemma lem5820829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5820830 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5820831 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5820836 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820837 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5820836 A B f x). Qed.
Lemma lem5820839 {A B : Type'} (f : A -> B) (a : A) : (f a) = (@I (A -> B) f a).
Proof. exact (@lem5820837 A B f a). Qed.
Lemma lem5820848 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820849 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem5820848 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem5820850 {A : Type'} (s : A -> Prop) : (@DELETE A s) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s).
Proof. exact (@lem5820849 A (@DELETE A) s). Qed.
Lemma lem5820851 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5820852 {A : Type'} (s : A -> Prop) (a : A) : (@DELETE A s a) = (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s a).
Proof. exact (MK_COMB (@lem5820850 A s) (@lem5820851 A a)). Qed.
Lemma lem5820854 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820855 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5820854 A (A -> Prop) f x). Qed.
Lemma lem5820856 {A : Type'} (s : A -> Prop) (a : A) : (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s a) = (term542 A s a).
Proof. exact (@lem5820855 A (@I ((A -> Prop) -> A -> A -> Prop) (@DELETE A) s) a). Qed.
Lemma lem5820858 {A : Type'} (s : A -> Prop) (a : A) : (@DELETE A s a) = (term542 A s a).
Proof. exact (TRANS (@lem5820852 A s a) (@lem5820856 A s a)). Qed.
Lemma lem5820859 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820860 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5820861 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) : (term657 A B op s a) = (term658 A B op s a).
Proof. exact (MK_COMB (@lem5820860 A B op) (@lem5820858 A s a)). Qed.
Lemma lem5820862 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term659 A B op s a f) = (term660 A B op s a f).
Proof. exact (MK_COMB (@lem5820861 A B op s a) (@lem5820859 A B f)). Qed.
Lemma lem5820864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820865 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820864 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5820866 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5820865 A B (@iterate B A) op). Qed.
Lemma lem5820867 {A : Type'} (s : A -> Prop) (a : A) : (term542 A s a) = (term542 A s a).
Proof. exact (eq_refl (term542 A s a)). Qed.
Lemma lem5820868 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) : (term658 A B op s a) = (term661 A B op s a).
Proof. exact (MK_COMB (@lem5820866 A B op) (@lem5820867 A s a)). Qed.
Lemma lem5820870 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820871 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820870 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5820872 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) : (term661 A B op s a) = (term662 A B op s a).
Proof. exact (@lem5820871 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) (term542 A s a)). Qed.
Lemma lem5820873 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) : (term658 A B op s a) = (term662 A B op s a).
Proof. exact (TRANS (@lem5820868 A B op s a) (@lem5820872 A B op s a)). Qed.
Lemma lem5820874 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820875 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term660 A B op s a f) = (term663 A B op s a f).
Proof. exact (MK_COMB (@lem5820873 A B op s a) (@lem5820874 A B f)). Qed.
Lemma lem5820877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820878 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5820877 (A -> B) B f x). Qed.
Lemma lem5820879 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term663 A B op s a f) = (term664 A B op s a f).
Proof. exact (@lem5820878 A B (term662 A B op s a) f). Qed.
Lemma lem5820880 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term660 A B op s a f) = (term664 A B op s a f).
Proof. exact (TRANS (@lem5820875 A B op s a f) (@lem5820879 A B op s a f)). Qed.
Lemma lem5820881 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term659 A B op s a f) = (term664 A B op s a f).
Proof. exact (TRANS (@lem5820862 A B op s a f) (@lem5820880 A B op s a f)). Qed.
Lemma lem5820882 {A B : Type'} (op : type1400 B) (f : A -> B) (a : A) : (term614 A B op f a) = (term615 A B op f a).
Proof. exact (MK_COMB (@lem5820831 B op) (@lem5820839 A B f a)). Qed.
Lemma lem5820883 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term180 A B op s a f) = (term665 A B op s a f).
Proof. exact (MK_COMB (@lem5820882 A B op f a) (@lem5820881 A B op s a f)). Qed.
Lemma lem5820885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820886 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5820885 B (B -> B) f x). Qed.
Lemma lem5820887 {A B : Type'} (op : type1400 B) (f : A -> B) (a : A) : (term615 A B op f a) = (term617 A B op f a).
Proof. exact (@lem5820886 B op (@I (A -> B) f a)). Qed.
Lemma lem5820888 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term664 A B op s a f) = (term664 A B op s a f).
Proof. exact (eq_refl (term664 A B op s a f)). Qed.
Lemma lem5820889 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term665 A B op s a f) = (term666 A B op s a f).
Proof. exact (MK_COMB (@lem5820887 A B op f a) (@lem5820888 A B op s a f)). Qed.
Lemma lem5820891 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820892 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5820891 B B f x). Qed.
Lemma lem5820893 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term666 A B op s a f) = (term667 A B op s a f).
Proof. exact (@lem5820892 B (term617 A B op f a) (term664 A B op s a f)). Qed.
Lemma lem5820894 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term665 A B op s a f) = (term667 A B op s a f).
Proof. exact (TRANS (@lem5820889 A B op s a f) (@lem5820893 A B op s a f)). Qed.
Lemma lem5820895 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term180 A B op s a f) = (term667 A B op s a f).
Proof. exact (TRANS (@lem5820883 A B op s a f) (@lem5820894 A B op s a f)). Qed.
Lemma lem5820904 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820905 {A B : Type'} (f : type750 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820904 (type1400 B) (type632 A B) f x). Qed.
Lemma lem5820906 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5820905 A B (@iterate B A) op). Qed.
Lemma lem5820907 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5820908 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s).
Proof. exact (MK_COMB (@lem5820906 A B op) (@lem5820907 A s)). Qed.
Lemma lem5820910 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820911 {A B : Type'} (f : type632 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> B) f x).
Proof. exact (@lem5820910 (A -> Prop) (type570 A B) f x). Qed.
Lemma lem5820912 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op s) = (term611 A B op s).
Proof. exact (@lem5820911 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) s). Qed.
Lemma lem5820913 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (@iterate B A op s) = (term611 A B op s).
Proof. exact (TRANS (@lem5820908 A B op s) (@lem5820912 A B op s)). Qed.
Lemma lem5820914 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5820915 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term612 A B op s f).
Proof. exact (MK_COMB (@lem5820913 A B op s) (@lem5820914 A B f)). Qed.
Lemma lem5820917 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820918 {A B : Type'} (f : type570 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> B) f x).
Proof. exact (@lem5820917 (A -> B) B f x). Qed.
Lemma lem5820919 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term612 A B op s f) = (term613 A B op s f).
Proof. exact (@lem5820918 A B (term611 A B op s) f). Qed.
Lemma lem5820921 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term613 A B op s f).
Proof. exact (TRANS (@lem5820915 A B op s f) (@lem5820919 A B op s f)). Qed.
Lemma lem5820922 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term668 A B op s a f) = (term669 A B op s a f).
Proof. exact (MK_COMB (@lem5820830 B) (@lem5820895 A B op s a f)). Qed.
Lemma lem5820923 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term180 A B op s a f) = (@iterate B A op s f)) = ((term667 A B op s a f) = (term613 A B op s f)).
Proof. exact (MK_COMB (@lem5820922 A B op s a f) (@lem5820921 A B op s f)). Qed.
Lemma lem5820924 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term670 A B a op s f) = (term671 A B a op s f).
Proof. exact (MK_COMB (@lem5820829) (@lem5820923 A B a op s f)). Qed.
Lemma lem5820931 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820932 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5820931 A (type686 A) f x). Qed.
Lemma lem5820933 {A : Type'} (a : A) : (@IN A a) = (@I (A -> (A -> Prop) -> Prop) (@IN A) a).
Proof. exact (@lem5820932 A (@IN A) a). Qed.
Lemma lem5820934 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5820935 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) a s).
Proof. exact (MK_COMB (@lem5820933 A a) (@lem5820934 A s)). Qed.
Lemma lem5820937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820938 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5820937 (A -> Prop) Prop f x). Qed.
Lemma lem5820939 {A : Type'} (a : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) a s) = (term548 A a s).
Proof. exact (@lem5820938 A (@I (A -> (A -> Prop) -> Prop) (@IN A) a) s). Qed.
Lemma lem5820941 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = (term548 A a s).
Proof. exact (TRANS (@lem5820935 A a s) (@lem5820939 A a s)). Qed.
Lemma lem5820946 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820947 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5820946 (A -> Prop) Prop f x). Qed.
Lemma lem5820949 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5820947 A (@FINITE A) s). Qed.
Lemma lem5820950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5820951 {A : Type'} (s : A -> Prop) : (term672 A s) = (term673 A s).
Proof. exact (MK_COMB (@lem5820950) (@lem5820949 A s)). Qed.
Lemma lem5820952 {A : Type'} (a : A) (s : A -> Prop) : (term179 A a s) = (term674 A a s).
Proof. exact (MK_COMB (@lem5820951 A s) (@lem5820941 A a s)). Qed.
Lemma lem5820953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5820954 {A : Type'} (a : A) (s : A -> Prop) : (term675 A a s) = (term676 A a s).
Proof. exact (MK_COMB (@lem5820953) (@lem5820952 A a s)). Qed.
Lemma lem5820955 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term178 A B a op s f) = (term677 A B a op s f).
Proof. exact (MK_COMB (@lem5820954 A a s) (@lem5820924 A B a op s f)). Qed.
Lemma lem5820960 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5820961 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem5820960 (type1400 B) Prop f x). Qed.
Lemma lem5820963 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5820961 B (@monoidal B) op). Qed.
Lemma lem5820964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5820965 {B : Type'} (op : type1400 B) : (term208 B op) = (term678 B op).
Proof. exact (MK_COMB (@lem5820964) (@lem5820963 B op)). Qed.
Lemma lem5820966 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term258 A B a op s f) = (term679 A B a op s f).
Proof. exact (MK_COMB (@lem5820965 B op) (@lem5820955 A B a op s f)). Qed.
Lemma lem5820967 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term679 A B a op s f.
Proof. exact (EQ_MP (@lem5820966 A B a op s f) (@lem5818532 A B a op s f h1)). Qed.
Lemma lem5820968 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term677 A B a op s f.
Proof. exact (proj2 (@lem5820967 A B a op s f h1)). Qed.
Lemma lem5820971 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term674 A a s.
Proof. exact (proj1 (@lem5820968 A B a op s f h1)). Qed.
Lemma lem5820975 {A : Type'} (h1 : term7 A) : term600 A.
Proof. exact (proj1 (@lem5819576 A h1)). Qed.
Lemma lem5820980 {A : Type'} (h1 : term8 A) : term573 A.
Proof. exact (proj2 (@lem5819246 A h1)). Qed.
Lemma lem5821025 {A : Type'} (x : A) (s : A -> Prop) : (term552 A x s) = (term552 A x s).
Proof. exact (eq_refl (term552 A x s)). Qed.
Lemma lem5821026 {A : Type'} (x : A) : (term553 A x) = (term553 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5821025 A x s)). Qed.
Lemma lem5821027 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5821028 {A : Type'} (x : A) : (term554 A x) = (term554 A x).
Proof. exact (MK_COMB (@lem5821027 A) (@lem5821026 A x)). Qed.
Lemma lem5821029 {A : Type'} : (term555 A) = (term555 A).
Proof. exact (fun_ext (fun x : A => @lem5821028 A x)). Qed.
Lemma lem5821030 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5821032 {A : Type'} : (term556 A) = (term556 A).
Proof. exact (MK_COMB (@lem5821030 A) (@lem5821029 A)). Qed.
Lemma lem5821033 {A : Type'} (h1 : term9 A) : term556 A.
Proof. exact (EQ_MP (@lem5821032 A) (@lem5818730 A h1)). Qed.
Lemma lem5821763 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term294 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5821764 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term517 A B P Q) = (term516 A B P Q).
Proof. exact (@lem5821763 (A -> B) P Q). Qed.
Lemma lem5821765 {A B : Type'} (op : type1400 B) : (term680 A B op) = (term681 A B op).
Proof. exact (@lem5821764 A B (term638 A B op) (term630 A B op)). Qed.
Lemma lem5821766 {A B : Type'} (op : type1400 B) (f : A -> B) : (term682 A B op f) = (term637 A B op f).
Proof. exact (eq_refl (term682 A B op f)). Qed.
Lemma lem5821767 {A B : Type'} (op : type1400 B) : (term683 A B op) = (term638 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5821766 A B op f)). Qed.
Lemma lem5821768 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821769 {A B : Type'} (op : type1400 B) : (term684 A B op) = (term639 A B op).
Proof. exact (MK_COMB (@lem5821768 A B) (@lem5821767 A B op)). Qed.
Lemma lem5821770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5821771 {A B : Type'} (op : type1400 B) : (term685 A B op) = (term640 A B op).
Proof. exact (MK_COMB (@lem5821770) (@lem5821769 A B op)). Qed.
Lemma lem5821772 {A B : Type'} (op : type1400 B) (f : A -> B) : (term686 A B op f) = (term629 A B op f).
Proof. exact (eq_refl (term686 A B op f)). Qed.
Lemma lem5821773 {A B : Type'} (op : type1400 B) : (term687 A B op) = (term630 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5821772 A B op f)). Qed.
Lemma lem5821774 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821775 {A B : Type'} (op : type1400 B) : (term688 A B op) = (term631 A B op).
Proof. exact (MK_COMB (@lem5821774 A B) (@lem5821773 A B op)). Qed.
Lemma lem5821776 {A B : Type'} (op : type1400 B) : (term680 A B op) = (term641 A B op).
Proof. exact (MK_COMB (@lem5821771 A B op) (@lem5821775 A B op)). Qed.
Lemma lem5821777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821778 {A B : Type'} (op : type1400 B) : (term689 A B op) = (term690 A B op).
Proof. exact (MK_COMB (@lem5821777) (@lem5821776 A B op)). Qed.
Lemma lem5821779 {A B : Type'} (op : type1400 B) (f : A -> B) : (term682 A B op f) = (term637 A B op f).
Proof. exact (eq_refl (term682 A B op f)). Qed.
Lemma lem5821780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5821781 {A B : Type'} (op : type1400 B) (f : A -> B) : (term691 A B op f) = (term692 A B op f).
Proof. exact (MK_COMB (@lem5821780) (@lem5821779 A B op f)). Qed.
Lemma lem5821782 {A B : Type'} (op : type1400 B) (f : A -> B) : (term686 A B op f) = (term629 A B op f).
Proof. exact (eq_refl (term686 A B op f)). Qed.
Lemma lem5821783 {A B : Type'} (op : type1400 B) (f : A -> B) : (term693 A B op f) = (term694 A B op f).
Proof. exact (MK_COMB (@lem5821781 A B op f) (@lem5821782 A B op f)). Qed.
Lemma lem5821784 {A B : Type'} (op : type1400 B) : (term695 A B op) = (term696 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5821783 A B op f)). Qed.
Lemma lem5821785 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821786 {A B : Type'} (op : type1400 B) : (term681 A B op) = (term697 A B op).
Proof. exact (MK_COMB (@lem5821785 A B) (@lem5821784 A B op)). Qed.
Lemma lem5821787 {A B : Type'} (op : type1400 B) : ((term680 A B op) = (term681 A B op)) = ((term641 A B op) = (term697 A B op)).
Proof. exact (MK_COMB (@lem5821778 A B op) (@lem5821786 A B op)). Qed.
Lemma lem5821788 {A B : Type'} (op : type1400 B) : (term641 A B op) = (term697 A B op).
Proof. exact (EQ_MP (@lem5821787 A B op) (@lem5821765 A B op)). Qed.
Lemma lem5821790 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term294 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5821791 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term294 A P Q).
Proof. exact (@lem5821790 A P Q). Qed.
Lemma lem5821792 {A B : Type'} (op : type1400 B) (f : A -> B) : (term698 A B op f) = (term699 A B op f).
Proof. exact (@lem5821791 A (term636 A B op f) (term628 A B op f)). Qed.
Lemma lem5821793 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term700 A B op f x) = (term635 A B x op f).
Proof. exact (eq_refl (term700 A B op f x)). Qed.
Lemma lem5821794 {A B : Type'} (op : type1400 B) (f : A -> B) : (term701 A B op f) = (term636 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5821793 A B x op f)). Qed.
Lemma lem5821795 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5821796 {A B : Type'} (op : type1400 B) (f : A -> B) : (term702 A B op f) = (term637 A B op f).
Proof. exact (MK_COMB (@lem5821795 A) (@lem5821794 A B op f)). Qed.
Lemma lem5821797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5821798 {A B : Type'} (op : type1400 B) (f : A -> B) : (term703 A B op f) = (term692 A B op f).
Proof. exact (MK_COMB (@lem5821797) (@lem5821796 A B op f)). Qed.
Lemma lem5821799 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term704 A B op f x) = (term627 A B x op f).
Proof. exact (eq_refl (term704 A B op f x)). Qed.
Lemma lem5821800 {A B : Type'} (op : type1400 B) (f : A -> B) : (term705 A B op f) = (term628 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5821799 A B x op f)). Qed.
Lemma lem5821801 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5821802 {A B : Type'} (op : type1400 B) (f : A -> B) : (term706 A B op f) = (term629 A B op f).
Proof. exact (MK_COMB (@lem5821801 A) (@lem5821800 A B op f)). Qed.
Lemma lem5821803 {A B : Type'} (op : type1400 B) (f : A -> B) : (term698 A B op f) = (term694 A B op f).
Proof. exact (MK_COMB (@lem5821798 A B op f) (@lem5821802 A B op f)). Qed.
Lemma lem5821804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821805 {A B : Type'} (op : type1400 B) (f : A -> B) : (term707 A B op f) = (term708 A B op f).
Proof. exact (MK_COMB (@lem5821804) (@lem5821803 A B op f)). Qed.
Lemma lem5821806 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term700 A B op f x) = (term635 A B x op f).
Proof. exact (eq_refl (term700 A B op f x)). Qed.
Lemma lem5821807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5821808 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term709 A B op f x) = (term710 A B x op f).
Proof. exact (MK_COMB (@lem5821807) (@lem5821806 A B x op f)). Qed.
Lemma lem5821809 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term704 A B op f x) = (term627 A B x op f).
Proof. exact (eq_refl (term704 A B op f x)). Qed.
Lemma lem5821810 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term711 A B op f x) = (term712 A B x op f).
Proof. exact (MK_COMB (@lem5821808 A B x op f) (@lem5821809 A B x op f)). Qed.
Lemma lem5821811 {A B : Type'} (op : type1400 B) (f : A -> B) : (term713 A B op f) = (term714 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5821810 A B x op f)). Qed.
Lemma lem5821812 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5821813 {A B : Type'} (op : type1400 B) (f : A -> B) : (term699 A B op f) = (term715 A B op f).
Proof. exact (MK_COMB (@lem5821812 A) (@lem5821811 A B op f)). Qed.
Lemma lem5821814 {A B : Type'} (op : type1400 B) (f : A -> B) : ((term698 A B op f) = (term699 A B op f)) = ((term694 A B op f) = (term715 A B op f)).
Proof. exact (MK_COMB (@lem5821805 A B op f) (@lem5821813 A B op f)). Qed.
Lemma lem5821815 {A B : Type'} (op : type1400 B) (f : A -> B) : (term694 A B op f) = (term715 A B op f).
Proof. exact (EQ_MP (@lem5821814 A B op f) (@lem5821792 A B op f)). Qed.
Lemma lem5821817 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term294 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5821818 {A : Type'} (P : type686 A) (Q : type686 A) : (term341 A P Q) = (term340 A P Q).
Proof. exact (@lem5821817 (A -> Prop) P Q). Qed.
Lemma lem5821819 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term716 A B x op f) = (term717 A B x op f).
Proof. exact (@lem5821818 A (term634 A B x op f) (term626 A B x op f)). Qed.
Lemma lem5821820 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term718 A B x op f s) = (term633 A B x op s f).
Proof. exact (eq_refl (term718 A B x op f s)). Qed.
Lemma lem5821821 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term719 A B x op f) = (term634 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5821820 A B x op s f)). Qed.
Lemma lem5821822 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5821823 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term720 A B x op f) = (term635 A B x op f).
Proof. exact (MK_COMB (@lem5821822 A) (@lem5821821 A B x op f)). Qed.
Lemma lem5821824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5821825 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term721 A B x op f) = (term710 A B x op f).
Proof. exact (MK_COMB (@lem5821824) (@lem5821823 A B x op f)). Qed.
Lemma lem5821826 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term722 A B x op f s) = (term625 A B x op s f).
Proof. exact (eq_refl (term722 A B x op f s)). Qed.
Lemma lem5821827 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term723 A B x op f) = (term626 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5821826 A B x op s f)). Qed.
Lemma lem5821828 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5821829 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term724 A B x op f) = (term627 A B x op f).
Proof. exact (MK_COMB (@lem5821828 A) (@lem5821827 A B x op f)). Qed.
Lemma lem5821830 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term716 A B x op f) = (term712 A B x op f).
Proof. exact (MK_COMB (@lem5821825 A B x op f) (@lem5821829 A B x op f)). Qed.
Lemma lem5821831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821832 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term725 A B x op f) = (term726 A B x op f).
Proof. exact (MK_COMB (@lem5821831) (@lem5821830 A B x op f)). Qed.
Lemma lem5821833 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term718 A B x op f s) = (term633 A B x op s f).
Proof. exact (eq_refl (term718 A B x op f s)). Qed.
Lemma lem5821834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5821835 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term727 A B x op f s) = (term728 A B x op s f).
Proof. exact (MK_COMB (@lem5821834) (@lem5821833 A B x op s f)). Qed.
Lemma lem5821836 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term722 A B x op f s) = (term625 A B x op s f).
Proof. exact (eq_refl (term722 A B x op f s)). Qed.
Lemma lem5821837 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term729 A B x op f s) = (term730 A B x op s f).
Proof. exact (MK_COMB (@lem5821835 A B x op s f) (@lem5821836 A B x op s f)). Qed.
Lemma lem5821838 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term731 A B x op f) = (term732 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5821837 A B x op s f)). Qed.
Lemma lem5821839 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5821840 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term717 A B x op f) = (term733 A B x op f).
Proof. exact (MK_COMB (@lem5821839 A) (@lem5821838 A B x op f)). Qed.
Lemma lem5821841 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : ((term716 A B x op f) = (term717 A B x op f)) = ((term712 A B x op f) = (term733 A B x op f)).
Proof. exact (MK_COMB (@lem5821832 A B x op f) (@lem5821840 A B x op f)). Qed.
Lemma lem5821842 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term712 A B x op f) = (term733 A B x op f).
Proof. exact (EQ_MP (@lem5821841 A B x op f) (@lem5821819 A B x op f)). Qed.
Lemma lem5821843 {A B : Type'} (op : type1400 B) (f : A -> B) : (term714 A B op f) = (term734 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5821842 A B x op f)). Qed.
Lemma lem5821844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5821845 {A B : Type'} (op : type1400 B) (f : A -> B) : (term715 A B op f) = (term735 A B op f).
Proof. exact (MK_COMB (@lem5821844 A) (@lem5821843 A B op f)). Qed.
Lemma lem5821846 {A B : Type'} (op : type1400 B) (f : A -> B) : (term694 A B op f) = (term735 A B op f).
Proof. exact (TRANS (@lem5821815 A B op f) (@lem5821845 A B op f)). Qed.
Lemma lem5821847 {A B : Type'} (op : type1400 B) : (term696 A B op) = (term736 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5821846 A B op f)). Qed.
Lemma lem5821848 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821849 {A B : Type'} (op : type1400 B) : (term697 A B op) = (term737 A B op).
Proof. exact (MK_COMB (@lem5821848 A B) (@lem5821847 A B op)). Qed.
Lemma lem5821850 {A B : Type'} (op : type1400 B) : (term641 A B op) = (term737 A B op).
Proof. exact (TRANS (@lem5821788 A B op) (@lem5821849 A B op)). Qed.
Lemma lem5821851 {_120477 B : Type'} (op : type1400 B) : (term649 _120477 B op) = (term649 _120477 B op).
Proof. exact (eq_refl (term649 _120477 B op)). Qed.
Lemma lem5821852 {_120477 A B : Type'} (op : type1400 B) : (term650 _120477 A B op) = (term738 _120477 A B op).
Proof. exact (MK_COMB (@lem5821851 _120477 B op) (@lem5821850 A B op)). Qed.
Lemma lem5821856 {A : Type'} (P : A -> Prop) (Q : Prop) : (term739 A P Q) = (term740 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5821857 {_120477 B : Type'} (P : type572 _120477 B) (Q : Prop) : (term741 _120477 B P Q) = (term742 _120477 B P Q).
Proof. exact (@lem5821856 (_120477 -> B) P Q). Qed.
Lemma lem5821858 {_120477 A B : Type'} (op : type1400 B) : (term743 _120477 A B op) = (term744 _120477 A B op).
Proof. exact (@lem5821857 _120477 B (term647 _120477 B op) (term737 A B op)). Qed.
Lemma lem5821859 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term745 _120477 B op f) = ((term644 _120477 B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (eq_refl (term745 _120477 B op f)). Qed.
Lemma lem5821860 {_120477 B : Type'} (op : type1400 B) : (term746 _120477 B op) = (term647 _120477 B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5821859 _120477 B f op)). Qed.
Lemma lem5821861 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5821862 {_120477 B : Type'} (op : type1400 B) : (term747 _120477 B op) = (term648 _120477 B op).
Proof. exact (MK_COMB (@lem5821861 _120477 B) (@lem5821860 _120477 B op)). Qed.
Lemma lem5821863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5821864 {_120477 B : Type'} (op : type1400 B) : (term748 _120477 B op) = (term649 _120477 B op).
Proof. exact (MK_COMB (@lem5821863) (@lem5821862 _120477 B op)). Qed.
Lemma lem5821865 {A B : Type'} (op : type1400 B) : (term737 A B op) = (term737 A B op).
Proof. exact (eq_refl (term737 A B op)). Qed.
Lemma lem5821866 {_120477 A B : Type'} (op : type1400 B) : (term743 _120477 A B op) = (term738 _120477 A B op).
Proof. exact (MK_COMB (@lem5821864 _120477 B op) (@lem5821865 A B op)). Qed.
Lemma lem5821867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821868 {_120477 A B : Type'} (op : type1400 B) : (term749 _120477 A B op) = (term750 _120477 A B op).
Proof. exact (MK_COMB (@lem5821867) (@lem5821866 _120477 A B op)). Qed.
Lemma lem5821869 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term745 _120477 B op f) = ((term644 _120477 B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (eq_refl (term745 _120477 B op f)). Qed.
Lemma lem5821870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5821871 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term751 _120477 B op f) = (term752 _120477 B f op).
Proof. exact (MK_COMB (@lem5821870) (@lem5821869 _120477 B f op)). Qed.
Lemma lem5821872 {A B : Type'} (op : type1400 B) : (term737 A B op) = (term737 A B op).
Proof. exact (eq_refl (term737 A B op)). Qed.
Lemma lem5821873 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term753 _120477 A B f op) = (term754 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821871 _120477 B f op) (@lem5821872 A B op)). Qed.
Lemma lem5821874 {_120477 A B : Type'} (op : type1400 B) : (term755 _120477 A B op) = (term756 _120477 A B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5821873 _120477 A B f op)). Qed.
Lemma lem5821875 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5821876 {_120477 A B : Type'} (op : type1400 B) : (term744 _120477 A B op) = (term757 _120477 A B op).
Proof. exact (MK_COMB (@lem5821875 _120477 B) (@lem5821874 _120477 A B op)). Qed.
Lemma lem5821877 {_120477 A B : Type'} (op : type1400 B) : ((term743 _120477 A B op) = (term744 _120477 A B op)) = ((term738 _120477 A B op) = (term757 _120477 A B op)).
Proof. exact (MK_COMB (@lem5821868 _120477 A B op) (@lem5821876 _120477 A B op)). Qed.
Lemma lem5821878 {_120477 A B : Type'} (op : type1400 B) : (term738 _120477 A B op) = (term757 _120477 A B op).
Proof. exact (EQ_MP (@lem5821877 _120477 A B op) (@lem5821858 _120477 A B op)). Qed.
Lemma lem5821880 {A : Type'} (P : Prop) (Q : A -> Prop) : (term758 A P Q) = (term759 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5821881 {A B : Type'} (P : Prop) (Q : type572 A B) : (term760 A B P Q) = (term761 A B P Q).
Proof. exact (@lem5821880 (A -> B) P Q). Qed.
Lemma lem5821882 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term762 _120477 A B f op) = (term763 _120477 A B f op).
Proof. exact (@lem5821881 A B ((term644 _120477 B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term736 A B op)). Qed.
Lemma lem5821883 {A B : Type'} (op : type1400 B) (f : A -> B) : (term764 A B op f) = (term735 A B op f).
Proof. exact (eq_refl (term764 A B op f)). Qed.
Lemma lem5821884 {A B : Type'} (op : type1400 B) : (term765 A B op) = (term736 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5821883 A B op f)). Qed.
Lemma lem5821885 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821886 {A B : Type'} (op : type1400 B) : (term766 A B op) = (term737 A B op).
Proof. exact (MK_COMB (@lem5821885 A B) (@lem5821884 A B op)). Qed.
Lemma lem5821887 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term752 _120477 B f op) = (term752 _120477 B f op).
Proof. exact (eq_refl (term752 _120477 B f op)). Qed.
Lemma lem5821888 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term762 _120477 A B f op) = (term754 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821887 _120477 B f op) (@lem5821886 A B op)). Qed.
Lemma lem5821889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821890 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term767 _120477 A B f op) = (term768 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821889) (@lem5821888 _120477 A B f op)). Qed.
Lemma lem5821891 {A B : Type'} (op : type1400 B) (f : A -> B) : (term764 A B op f) = (term735 A B op f).
Proof. exact (eq_refl (term764 A B op f)). Qed.
Lemma lem5821892 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term752 _120477 B f op) = (term752 _120477 B f op).
Proof. exact (eq_refl (term752 _120477 B f op)). Qed.
Lemma lem5821893 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term769 _120477 A B f op f') = (term770 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5821892 _120477 B f op) (@lem5821891 A B op f')). Qed.
Lemma lem5821894 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term771 _120477 A B f op) = (term772 _120477 A B f op).
Proof. exact (fun_ext (fun f' : A -> B => @lem5821893 _120477 A B f op f')). Qed.
Lemma lem5821895 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821896 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term763 _120477 A B f op) = (term773 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821895 A B) (@lem5821894 _120477 A B f op)). Qed.
Lemma lem5821897 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : ((term762 _120477 A B f op) = (term763 _120477 A B f op)) = ((term754 _120477 A B f op) = (term773 _120477 A B f op)).
Proof. exact (MK_COMB (@lem5821890 _120477 A B f op) (@lem5821896 _120477 A B f op)). Qed.
Lemma lem5821898 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term754 _120477 A B f op) = (term773 _120477 A B f op).
Proof. exact (EQ_MP (@lem5821897 _120477 A B f op) (@lem5821882 _120477 A B f op)). Qed.
Lemma lem5821900 {A : Type'} (P : Prop) (Q : A -> Prop) : (term758 A P Q) = (term759 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5821901 {A : Type'} (P : Prop) (Q : A -> Prop) : (term758 A P Q) = (term759 A P Q).
Proof. exact (@lem5821900 A P Q). Qed.
Lemma lem5821902 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term774 _120477 A B f op f') = (term775 _120477 A B f op f').
Proof. exact (@lem5821901 A ((term644 _120477 B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term734 A B op f')). Qed.
Lemma lem5821903 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term776 A B op f x) = (term733 A B x op f).
Proof. exact (eq_refl (term776 A B op f x)). Qed.
Lemma lem5821904 {A B : Type'} (op : type1400 B) (f : A -> B) : (term777 A B op f) = (term734 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5821903 A B x op f)). Qed.
Lemma lem5821905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5821906 {A B : Type'} (op : type1400 B) (f : A -> B) : (term778 A B op f) = (term735 A B op f).
Proof. exact (MK_COMB (@lem5821905 A) (@lem5821904 A B op f)). Qed.
Lemma lem5821907 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term752 _120477 B f op) = (term752 _120477 B f op).
Proof. exact (eq_refl (term752 _120477 B f op)). Qed.
Lemma lem5821908 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term774 _120477 A B f op f') = (term770 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5821907 _120477 B f op) (@lem5821906 A B op f')). Qed.
Lemma lem5821909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821910 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term779 _120477 A B f op f') = (term780 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5821909) (@lem5821908 _120477 A B f op f')). Qed.
Lemma lem5821911 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term776 A B op f x) = (term733 A B x op f).
Proof. exact (eq_refl (term776 A B op f x)). Qed.
Lemma lem5821912 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term752 _120477 B f op) = (term752 _120477 B f op).
Proof. exact (eq_refl (term752 _120477 B f op)). Qed.
Lemma lem5821913 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term781 _120477 A B f op f' x) = (term782 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5821912 _120477 B f op) (@lem5821911 A B x op f')). Qed.
Lemma lem5821914 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term783 _120477 A B f op f') = (term784 _120477 A B f op f').
Proof. exact (fun_ext (fun x : A => @lem5821913 _120477 A B f x op f')). Qed.
Lemma lem5821915 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5821916 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term775 _120477 A B f op f') = (term785 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5821915 A) (@lem5821914 _120477 A B f op f')). Qed.
Lemma lem5821917 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : ((term774 _120477 A B f op f') = (term775 _120477 A B f op f')) = ((term770 _120477 A B f op f') = (term785 _120477 A B f op f')).
Proof. exact (MK_COMB (@lem5821910 _120477 A B f op f') (@lem5821916 _120477 A B f op f')). Qed.
Lemma lem5821918 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term770 _120477 A B f op f') = (term785 _120477 A B f op f').
Proof. exact (EQ_MP (@lem5821917 _120477 A B f op f') (@lem5821902 _120477 A B f op f')). Qed.
Lemma lem5821920 {A : Type'} (P : Prop) (Q : A -> Prop) : (term758 A P Q) = (term759 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5821921 {A : Type'} (P : Prop) (Q : type686 A) : (term786 A P Q) = (term787 A P Q).
Proof. exact (@lem5821920 (A -> Prop) P Q). Qed.
Lemma lem5821922 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term788 _120477 A B f x op f') = (term789 _120477 A B f x op f').
Proof. exact (@lem5821921 A ((term644 _120477 B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term732 A B x op f')). Qed.
Lemma lem5821923 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term790 A B x op f s) = (term730 A B x op s f).
Proof. exact (eq_refl (term790 A B x op f s)). Qed.
Lemma lem5821924 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term791 A B x op f) = (term732 A B x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5821923 A B x op s f)). Qed.
Lemma lem5821925 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5821926 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term792 A B x op f) = (term733 A B x op f).
Proof. exact (MK_COMB (@lem5821925 A) (@lem5821924 A B x op f)). Qed.
Lemma lem5821927 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term752 _120477 B f op) = (term752 _120477 B f op).
Proof. exact (eq_refl (term752 _120477 B f op)). Qed.
Lemma lem5821928 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term788 _120477 A B f x op f') = (term782 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5821927 _120477 B f op) (@lem5821926 A B x op f')). Qed.
Lemma lem5821929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821930 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term793 _120477 A B f x op f') = (term794 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5821929) (@lem5821928 _120477 A B f x op f')). Qed.
Lemma lem5821931 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term790 A B x op f s) = (term730 A B x op s f).
Proof. exact (eq_refl (term790 A B x op f s)). Qed.
Lemma lem5821932 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term752 _120477 B f op) = (term752 _120477 B f op).
Proof. exact (eq_refl (term752 _120477 B f op)). Qed.
Lemma lem5821933 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (s : A -> Prop) (f' : A -> B) : (term795 _120477 A B f x op f' s) = (term796 _120477 A B f x op s f').
Proof. exact (MK_COMB (@lem5821932 _120477 B f op) (@lem5821931 A B x op s f')). Qed.
Lemma lem5821934 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term797 _120477 A B f x op f') = (term798 _120477 A B f x op f').
Proof. exact (fun_ext (fun s : A -> Prop => @lem5821933 _120477 A B f x op s f')). Qed.
Lemma lem5821935 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5821936 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term789 _120477 A B f x op f') = (term799 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5821935 A) (@lem5821934 _120477 A B f x op f')). Qed.
Lemma lem5821937 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : ((term788 _120477 A B f x op f') = (term789 _120477 A B f x op f')) = ((term782 _120477 A B f x op f') = (term799 _120477 A B f x op f')).
Proof. exact (MK_COMB (@lem5821930 _120477 A B f x op f') (@lem5821936 _120477 A B f x op f')). Qed.
Lemma lem5821938 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term782 _120477 A B f x op f') = (term799 _120477 A B f x op f').
Proof. exact (EQ_MP (@lem5821937 _120477 A B f x op f') (@lem5821922 _120477 A B f x op f')). Qed.
Lemma lem5821939 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term784 _120477 A B f op f') = (term800 _120477 A B f op f').
Proof. exact (fun_ext (fun x : A => @lem5821938 _120477 A B f x op f')). Qed.
Lemma lem5821940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5821941 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term785 _120477 A B f op f') = (term801 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5821940 A) (@lem5821939 _120477 A B f op f')). Qed.
Lemma lem5821942 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term770 _120477 A B f op f') = (term801 _120477 A B f op f').
Proof. exact (TRANS (@lem5821918 _120477 A B f op f') (@lem5821941 _120477 A B f op f')). Qed.
Lemma lem5821943 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term772 _120477 A B f op) = (term802 _120477 A B f op).
Proof. exact (fun_ext (fun f' : A -> B => @lem5821942 _120477 A B f op f')). Qed.
Lemma lem5821944 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821945 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term773 _120477 A B f op) = (term803 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821944 A B) (@lem5821943 _120477 A B f op)). Qed.
Lemma lem5821946 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term754 _120477 A B f op) = (term803 _120477 A B f op).
Proof. exact (TRANS (@lem5821898 _120477 A B f op) (@lem5821945 _120477 A B f op)). Qed.
Lemma lem5821947 {_120477 A B : Type'} (op : type1400 B) : (term756 _120477 A B op) = (term804 _120477 A B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5821946 _120477 A B f op)). Qed.
Lemma lem5821948 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5821949 {_120477 A B : Type'} (op : type1400 B) : (term757 _120477 A B op) = (term805 _120477 A B op).
Proof. exact (MK_COMB (@lem5821948 _120477 B) (@lem5821947 _120477 A B op)). Qed.
Lemma lem5821950 {_120477 A B : Type'} (op : type1400 B) : (term738 _120477 A B op) = (term805 _120477 A B op).
Proof. exact (TRANS (@lem5821878 _120477 A B op) (@lem5821949 _120477 A B op)). Qed.
Lemma lem5821951 {_120477 A B : Type'} (op : type1400 B) : (term650 _120477 A B op) = (term805 _120477 A B op).
Proof. exact (TRANS (@lem5821852 _120477 A B op) (@lem5821950 _120477 A B op)). Qed.
Lemma lem5821952 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5821953 {_120477 A B : Type'} (op : type1400 B) : (term654 _120477 A B op) = (term806 _120477 A B op).
Proof. exact (MK_COMB (@lem5821952 B op) (@lem5821951 _120477 A B op)). Qed.
Lemma lem5821955 {A : Type'} (P : Prop) (Q : A -> Prop) : (term807 A P Q) = (term808 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5821956 {_120477 B : Type'} (P : Prop) (Q : type572 _120477 B) : (term809 _120477 B P Q) = (term810 _120477 B P Q).
Proof. exact (@lem5821955 (_120477 -> B) P Q). Qed.
Lemma lem5821957 {_120477 A B : Type'} (op : type1400 B) : (term811 _120477 A B op) = (term812 _120477 A B op).
Proof. exact (@lem5821956 _120477 B (term652 B op) (term804 _120477 A B op)). Qed.
Lemma lem5821958 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term813 _120477 A B op f) = (term803 _120477 A B f op).
Proof. exact (eq_refl (term813 _120477 A B op f)). Qed.
Lemma lem5821959 {_120477 A B : Type'} (op : type1400 B) : (term814 _120477 A B op) = (term804 _120477 A B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5821958 _120477 A B f op)). Qed.
Lemma lem5821960 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5821961 {_120477 A B : Type'} (op : type1400 B) : (term815 _120477 A B op) = (term805 _120477 A B op).
Proof. exact (MK_COMB (@lem5821960 _120477 B) (@lem5821959 _120477 A B op)). Qed.
Lemma lem5821962 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5821963 {_120477 A B : Type'} (op : type1400 B) : (term811 _120477 A B op) = (term806 _120477 A B op).
Proof. exact (MK_COMB (@lem5821962 B op) (@lem5821961 _120477 A B op)). Qed.
Lemma lem5821964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821965 {_120477 A B : Type'} (op : type1400 B) : (term816 _120477 A B op) = (term817 _120477 A B op).
Proof. exact (MK_COMB (@lem5821964) (@lem5821963 _120477 A B op)). Qed.
Lemma lem5821966 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term813 _120477 A B op f) = (term803 _120477 A B f op).
Proof. exact (eq_refl (term813 _120477 A B op f)). Qed.
Lemma lem5821967 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5821968 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term818 _120477 A B op f) = (term819 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821967 B op) (@lem5821966 _120477 A B f op)). Qed.
Lemma lem5821969 {_120477 A B : Type'} (op : type1400 B) : (term820 _120477 A B op) = (term821 _120477 A B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5821968 _120477 A B f op)). Qed.
Lemma lem5821970 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5821971 {_120477 A B : Type'} (op : type1400 B) : (term812 _120477 A B op) = (term822 _120477 A B op).
Proof. exact (MK_COMB (@lem5821970 _120477 B) (@lem5821969 _120477 A B op)). Qed.
Lemma lem5821972 {_120477 A B : Type'} (op : type1400 B) : ((term811 _120477 A B op) = (term812 _120477 A B op)) = ((term806 _120477 A B op) = (term822 _120477 A B op)).
Proof. exact (MK_COMB (@lem5821965 _120477 A B op) (@lem5821971 _120477 A B op)). Qed.
Lemma lem5821973 {_120477 A B : Type'} (op : type1400 B) : (term806 _120477 A B op) = (term822 _120477 A B op).
Proof. exact (EQ_MP (@lem5821972 _120477 A B op) (@lem5821957 _120477 A B op)). Qed.
Lemma lem5821975 {A : Type'} (P : Prop) (Q : A -> Prop) : (term807 A P Q) = (term808 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5821976 {A B : Type'} (P : Prop) (Q : type572 A B) : (term809 A B P Q) = (term810 A B P Q).
Proof. exact (@lem5821975 (A -> B) P Q). Qed.
Lemma lem5821977 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term823 _120477 A B f op) = (term824 _120477 A B f op).
Proof. exact (@lem5821976 A B (term652 B op) (term802 _120477 A B f op)). Qed.
Lemma lem5821978 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term825 _120477 A B f op f') = (term801 _120477 A B f op f').
Proof. exact (eq_refl (term825 _120477 A B f op f')). Qed.
Lemma lem5821979 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term826 _120477 A B f op) = (term802 _120477 A B f op).
Proof. exact (fun_ext (fun f' : A -> B => @lem5821978 _120477 A B f op f')). Qed.
Lemma lem5821980 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821981 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term827 _120477 A B f op) = (term803 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821980 A B) (@lem5821979 _120477 A B f op)). Qed.
Lemma lem5821982 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5821983 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term823 _120477 A B f op) = (term819 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821982 B op) (@lem5821981 _120477 A B f op)). Qed.
Lemma lem5821984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5821985 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term828 _120477 A B f op) = (term829 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821984) (@lem5821983 _120477 A B f op)). Qed.
Lemma lem5821986 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term825 _120477 A B f op f') = (term801 _120477 A B f op f').
Proof. exact (eq_refl (term825 _120477 A B f op f')). Qed.
Lemma lem5821987 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5821988 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term830 _120477 A B f op f') = (term831 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5821987 B op) (@lem5821986 _120477 A B f op f')). Qed.
Lemma lem5821989 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term832 _120477 A B f op) = (term833 _120477 A B f op).
Proof. exact (fun_ext (fun f' : A -> B => @lem5821988 _120477 A B f op f')). Qed.
Lemma lem5821990 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5821991 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term824 _120477 A B f op) = (term834 _120477 A B f op).
Proof. exact (MK_COMB (@lem5821990 A B) (@lem5821989 _120477 A B f op)). Qed.
Lemma lem5821992 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : ((term823 _120477 A B f op) = (term824 _120477 A B f op)) = ((term819 _120477 A B f op) = (term834 _120477 A B f op)).
Proof. exact (MK_COMB (@lem5821985 _120477 A B f op) (@lem5821991 _120477 A B f op)). Qed.
Lemma lem5821993 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term819 _120477 A B f op) = (term834 _120477 A B f op).
Proof. exact (EQ_MP (@lem5821992 _120477 A B f op) (@lem5821977 _120477 A B f op)). Qed.
Lemma lem5821995 {A : Type'} (P : Prop) (Q : A -> Prop) : (term807 A P Q) = (term808 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5821996 {A : Type'} (P : Prop) (Q : A -> Prop) : (term807 A P Q) = (term808 A P Q).
Proof. exact (@lem5821995 A P Q). Qed.
Lemma lem5821997 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term835 _120477 A B f op f') = (term836 _120477 A B f op f').
Proof. exact (@lem5821996 A (term652 B op) (term800 _120477 A B f op f')). Qed.
Lemma lem5821998 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term837 _120477 A B f op f' x) = (term799 _120477 A B f x op f').
Proof. exact (eq_refl (term837 _120477 A B f op f' x)). Qed.
Lemma lem5821999 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term838 _120477 A B f op f') = (term800 _120477 A B f op f').
Proof. exact (fun_ext (fun x : A => @lem5821998 _120477 A B f x op f')). Qed.
Lemma lem5822000 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822001 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term839 _120477 A B f op f') = (term801 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5822000 A) (@lem5821999 _120477 A B f op f')). Qed.
Lemma lem5822002 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5822003 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term835 _120477 A B f op f') = (term831 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5822002 B op) (@lem5822001 _120477 A B f op f')). Qed.
Lemma lem5822004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5822005 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term840 _120477 A B f op f') = (term841 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5822004) (@lem5822003 _120477 A B f op f')). Qed.
Lemma lem5822006 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term837 _120477 A B f op f' x) = (term799 _120477 A B f x op f').
Proof. exact (eq_refl (term837 _120477 A B f op f' x)). Qed.
Lemma lem5822007 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5822008 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term842 _120477 A B f op f' x) = (term843 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5822007 B op) (@lem5822006 _120477 A B f x op f')). Qed.
Lemma lem5822009 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term844 _120477 A B f op f') = (term845 _120477 A B f op f').
Proof. exact (fun_ext (fun x : A => @lem5822008 _120477 A B f x op f')). Qed.
Lemma lem5822010 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822011 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term836 _120477 A B f op f') = (term846 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5822010 A) (@lem5822009 _120477 A B f op f')). Qed.
Lemma lem5822012 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : ((term835 _120477 A B f op f') = (term836 _120477 A B f op f')) = ((term831 _120477 A B f op f') = (term846 _120477 A B f op f')).
Proof. exact (MK_COMB (@lem5822005 _120477 A B f op f') (@lem5822011 _120477 A B f op f')). Qed.
Lemma lem5822013 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term831 _120477 A B f op f') = (term846 _120477 A B f op f').
Proof. exact (EQ_MP (@lem5822012 _120477 A B f op f') (@lem5821997 _120477 A B f op f')). Qed.
Lemma lem5822015 {A : Type'} (P : Prop) (Q : A -> Prop) : (term807 A P Q) = (term808 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5822016 {A : Type'} (P : Prop) (Q : type686 A) : (term847 A P Q) = (term848 A P Q).
Proof. exact (@lem5822015 (A -> Prop) P Q). Qed.
Lemma lem5822017 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term849 _120477 A B f x op f') = (term850 _120477 A B f x op f').
Proof. exact (@lem5822016 A (term652 B op) (term798 _120477 A B f x op f')). Qed.
Lemma lem5822018 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (s : A -> Prop) (f' : A -> B) : (term851 _120477 A B f x op f' s) = (term796 _120477 A B f x op s f').
Proof. exact (eq_refl (term851 _120477 A B f x op f' s)). Qed.
Lemma lem5822019 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term852 _120477 A B f x op f') = (term798 _120477 A B f x op f').
Proof. exact (fun_ext (fun s : A -> Prop => @lem5822018 _120477 A B f x op s f')). Qed.
Lemma lem5822020 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5822021 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term853 _120477 A B f x op f') = (term799 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5822020 A) (@lem5822019 _120477 A B f x op f')). Qed.
Lemma lem5822022 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5822023 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term849 _120477 A B f x op f') = (term843 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5822022 B op) (@lem5822021 _120477 A B f x op f')). Qed.
Lemma lem5822024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5822025 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term854 _120477 A B f x op f') = (term855 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5822024) (@lem5822023 _120477 A B f x op f')). Qed.
Lemma lem5822026 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (s : A -> Prop) (f' : A -> B) : (term851 _120477 A B f x op f' s) = (term796 _120477 A B f x op s f').
Proof. exact (eq_refl (term851 _120477 A B f x op f' s)). Qed.
Lemma lem5822027 {B : Type'} (op : type1400 B) : (term653 B op) = (term653 B op).
Proof. exact (eq_refl (term653 B op)). Qed.
Lemma lem5822028 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (s : A -> Prop) (f' : A -> B) : (term856 _120477 A B f x op f' s) = (term857 _120477 A B f x op s f').
Proof. exact (MK_COMB (@lem5822027 B op) (@lem5822026 _120477 A B f x op s f')). Qed.
Lemma lem5822029 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term858 _120477 A B f x op f') = (term859 _120477 A B f x op f').
Proof. exact (fun_ext (fun s : A -> Prop => @lem5822028 _120477 A B f x op s f')). Qed.
Lemma lem5822030 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5822031 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term850 _120477 A B f x op f') = (term860 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5822030 A) (@lem5822029 _120477 A B f x op f')). Qed.
Lemma lem5822032 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : ((term849 _120477 A B f x op f') = (term850 _120477 A B f x op f')) = ((term843 _120477 A B f x op f') = (term860 _120477 A B f x op f')).
Proof. exact (MK_COMB (@lem5822025 _120477 A B f x op f') (@lem5822031 _120477 A B f x op f')). Qed.
Lemma lem5822033 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term843 _120477 A B f x op f') = (term860 _120477 A B f x op f').
Proof. exact (EQ_MP (@lem5822032 _120477 A B f x op f') (@lem5822017 _120477 A B f x op f')). Qed.
Lemma lem5822034 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term845 _120477 A B f op f') = (term861 _120477 A B f op f').
Proof. exact (fun_ext (fun x : A => @lem5822033 _120477 A B f x op f')). Qed.
Lemma lem5822035 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822036 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term846 _120477 A B f op f') = (term862 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5822035 A) (@lem5822034 _120477 A B f op f')). Qed.
Lemma lem5822037 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term831 _120477 A B f op f') = (term862 _120477 A B f op f').
Proof. exact (TRANS (@lem5822013 _120477 A B f op f') (@lem5822036 _120477 A B f op f')). Qed.
Lemma lem5822038 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term833 _120477 A B f op) = (term863 _120477 A B f op).
Proof. exact (fun_ext (fun f' : A -> B => @lem5822037 _120477 A B f op f')). Qed.
Lemma lem5822039 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5822040 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term834 _120477 A B f op) = (term864 _120477 A B f op).
Proof. exact (MK_COMB (@lem5822039 A B) (@lem5822038 _120477 A B f op)). Qed.
Lemma lem5822041 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term819 _120477 A B f op) = (term864 _120477 A B f op).
Proof. exact (TRANS (@lem5821993 _120477 A B f op) (@lem5822040 _120477 A B f op)). Qed.
Lemma lem5822042 {_120477 A B : Type'} (op : type1400 B) : (term821 _120477 A B op) = (term865 _120477 A B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5822041 _120477 A B f op)). Qed.
Lemma lem5822043 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5822044 {_120477 A B : Type'} (op : type1400 B) : (term822 _120477 A B op) = (term866 _120477 A B op).
Proof. exact (MK_COMB (@lem5822043 _120477 B) (@lem5822042 _120477 A B op)). Qed.
Lemma lem5822045 {_120477 A B : Type'} (op : type1400 B) : (term806 _120477 A B op) = (term866 _120477 A B op).
Proof. exact (TRANS (@lem5821973 _120477 A B op) (@lem5822044 _120477 A B op)). Qed.
Lemma lem5822046 {_120477 A B : Type'} (op : type1400 B) : (term654 _120477 A B op) = (term866 _120477 A B op).
Proof. exact (TRANS (@lem5821953 _120477 A B op) (@lem5822045 _120477 A B op)). Qed.
Lemma lem5822047 {_120477 A B : Type'} : (term655 _120477 A B) = (term867 _120477 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5822046 _120477 A B op)). Qed.
Lemma lem5822048 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5822049 {_120477 A B : Type'} : (term656 _120477 A B) = (term868 _120477 A B).
Proof. exact (MK_COMB (@lem5822048 B) (@lem5822047 _120477 A B)). Qed.
Lemma lem5822087 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (s : A -> Prop) (f' : A -> B) : (term857 _120477 A B f x op s f') = (term869 _120477 A B f x op s f').
Proof. exact (@lem19490 ((term644 _120477 B op f) = (@I ((B -> B -> B) -> B) (@neutral B) op)) (term652 B op) (term730 A B x op s f')). Qed.
Lemma lem5822094 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term870 A B x op s f) = (term871 A B x op s f).
Proof. exact (@lem19490 (term633 A B x op s f) (term652 B op) (term625 A B x op s f)). Qed.
Lemma lem5822097 {_120477 B : Type'} (f : _120477 -> B) (op : type1400 B) : (term872 _120477 B f op) = (term872 _120477 B f op).
Proof. exact (eq_refl (term872 _120477 B f op)). Qed.
Lemma lem5822098 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (s : A -> Prop) (f' : A -> B) : (term869 _120477 A B f x op s f') = (term873 _120477 A B f x op s f').
Proof. exact (MK_COMB (@lem5822097 _120477 B f op) (@lem5822094 A B x op s f')). Qed.
Lemma lem5822100 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (s : A -> Prop) (f' : A -> B) : (term857 _120477 A B f x op s f') = (term873 _120477 A B f x op s f').
Proof. exact (TRANS (@lem5822087 _120477 A B f x op s f') (@lem5822098 _120477 A B f x op s f')). Qed.
Lemma lem5822101 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term859 _120477 A B f x op f') = (term874 _120477 A B f x op f').
Proof. exact (fun_ext (fun s : A -> Prop => @lem5822100 _120477 A B f x op s f')). Qed.
Lemma lem5822102 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5822103 {_120477 A B : Type'} (f : _120477 -> B) (x : A) (op : type1400 B) (f' : A -> B) : (term860 _120477 A B f x op f') = (term875 _120477 A B f x op f').
Proof. exact (MK_COMB (@lem5822102 A) (@lem5822101 _120477 A B f x op f')). Qed.
Lemma lem5822104 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term861 _120477 A B f op f') = (term876 _120477 A B f op f').
Proof. exact (fun_ext (fun x : A => @lem5822103 _120477 A B f x op f')). Qed.
Lemma lem5822105 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822106 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) (f' : A -> B) : (term862 _120477 A B f op f') = (term877 _120477 A B f op f').
Proof. exact (MK_COMB (@lem5822105 A) (@lem5822104 _120477 A B f op f')). Qed.
Lemma lem5822107 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term863 _120477 A B f op) = (term878 _120477 A B f op).
Proof. exact (fun_ext (fun f' : A -> B => @lem5822106 _120477 A B f op f')). Qed.
Lemma lem5822108 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5822109 {_120477 A B : Type'} (f : _120477 -> B) (op : type1400 B) : (term864 _120477 A B f op) = (term879 _120477 A B f op).
Proof. exact (MK_COMB (@lem5822108 A B) (@lem5822107 _120477 A B f op)). Qed.
Lemma lem5822110 {_120477 A B : Type'} (op : type1400 B) : (term865 _120477 A B op) = (term880 _120477 A B op).
Proof. exact (fun_ext (fun f : _120477 -> B => @lem5822109 _120477 A B f op)). Qed.
Lemma lem5822111 {_120477 B : Type'} : (@all (_120477 -> B)) = (@all (_120477 -> B)).
Proof. exact (eq_refl (@all (_120477 -> B))). Qed.
Lemma lem5822112 {_120477 A B : Type'} (op : type1400 B) : (term866 _120477 A B op) = (term881 _120477 A B op).
Proof. exact (MK_COMB (@lem5822111 _120477 B) (@lem5822110 _120477 A B op)). Qed.
Lemma lem5822113 {_120477 A B : Type'} : (term867 _120477 A B) = (term882 _120477 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5822112 _120477 A B op)). Qed.
Lemma lem5822114 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5822115 {_120477 A B : Type'} : (term868 _120477 A B) = (term883 _120477 A B).
Proof. exact (MK_COMB (@lem5822114 B) (@lem5822113 _120477 A B)). Qed.
Lemma lem5822116 {_120477 A B : Type'} : (term656 _120477 A B) = (term883 _120477 A B).
Proof. exact (TRANS (@lem5822049 _120477 A B) (@lem5822115 _120477 A B)). Qed.
Lemma lem5822117 {_120477 A B : Type'} (h1 : term99 _120477 A B) : term883 _120477 A B.
Proof. exact (EQ_MP (@lem5822116 _120477 A B) (@lem5820515 _120477 A B h1)). Qed.
Lemma lem5822491 {A : Type'} (P : A -> Prop) (Q : Prop) : (term391 A P Q) = (term390 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5822492 {A : Type'} (P : A -> Prop) (Q : Prop) : (term391 A P Q) = (term390 A P Q).
Proof. exact (@lem5822491 A P Q). Qed.
Lemma lem5822493 {A : Type'} (s : A -> Prop) : (term884 A s) = (term885 A s).
Proof. exact (@lem5822492 A (term595 A s) (term594 A s)). Qed.
Lemma lem5822494 {A : Type'} (s : A -> Prop) (x : A) : (term886 A s x) = (term586 A s x).
Proof. exact (eq_refl (term886 A s x)). Qed.
Lemma lem5822495 {A : Type'} (s : A -> Prop) : (term887 A s) = (term595 A s).
Proof. exact (fun_ext (fun x : A => @lem5822494 A s x)). Qed.
Lemma lem5822496 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822497 {A : Type'} (s : A -> Prop) : (term888 A s) = (term596 A s).
Proof. exact (MK_COMB (@lem5822496 A) (@lem5822495 A s)). Qed.
Lemma lem5822498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5822499 {A : Type'} (s : A -> Prop) : (term889 A s) = (term597 A s).
Proof. exact (MK_COMB (@lem5822498) (@lem5822497 A s)). Qed.
Lemma lem5822500 {A : Type'} (s : A -> Prop) : (term594 A s) = (term594 A s).
Proof. exact (eq_refl (term594 A s)). Qed.
Lemma lem5822501 {A : Type'} (s : A -> Prop) : (term884 A s) = (term598 A s).
Proof. exact (MK_COMB (@lem5822499 A s) (@lem5822500 A s)). Qed.
Lemma lem5822502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5822503 {A : Type'} (s : A -> Prop) : (term890 A s) = (term891 A s).
Proof. exact (MK_COMB (@lem5822502) (@lem5822501 A s)). Qed.
Lemma lem5822504 {A : Type'} (s : A -> Prop) (x : A) : (term886 A s x) = (term586 A s x).
Proof. exact (eq_refl (term886 A s x)). Qed.
Lemma lem5822505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5822506 {A : Type'} (s : A -> Prop) (x : A) : (term892 A s x) = (term893 A s x).
Proof. exact (MK_COMB (@lem5822505) (@lem5822504 A s x)). Qed.
Lemma lem5822507 {A : Type'} (s : A -> Prop) : (term594 A s) = (term594 A s).
Proof. exact (eq_refl (term594 A s)). Qed.
Lemma lem5822508 {A : Type'} (x : A) (s : A -> Prop) : (term894 A x s) = (term895 A x s).
Proof. exact (MK_COMB (@lem5822506 A s x) (@lem5822507 A s)). Qed.
Lemma lem5822509 {A : Type'} (s : A -> Prop) : (term896 A s) = (term897 A s).
Proof. exact (fun_ext (fun x : A => @lem5822508 A x s)). Qed.
Lemma lem5822510 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822511 {A : Type'} (s : A -> Prop) : (term885 A s) = (term898 A s).
Proof. exact (MK_COMB (@lem5822510 A) (@lem5822509 A s)). Qed.
Lemma lem5822512 {A : Type'} (s : A -> Prop) : ((term884 A s) = (term885 A s)) = ((term598 A s) = (term898 A s)).
Proof. exact (MK_COMB (@lem5822503 A s) (@lem5822511 A s)). Qed.
Lemma lem5822513 {A : Type'} (s : A -> Prop) : (term598 A s) = (term898 A s).
Proof. exact (EQ_MP (@lem5822512 A s) (@lem5822493 A s)). Qed.
Lemma lem5822514 {A : Type'} : (term599 A) = (term899 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5822513 A s)). Qed.
Lemma lem5822515 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5822516 {A : Type'} : (term600 A) = (term900 A).
Proof. exact (MK_COMB (@lem5822515 A) (@lem5822514 A)). Qed.
Lemma lem5822523 {A : Type'} (x : A) (s : A -> Prop) : (term895 A x s) = (term895 A x s).
Proof. exact (eq_refl (term895 A x s)). Qed.
Lemma lem5822524 {A : Type'} (s : A -> Prop) : (term897 A s) = (term897 A s).
Proof. exact (fun_ext (fun x : A => @lem5822523 A x s)). Qed.
Lemma lem5822525 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822526 {A : Type'} (s : A -> Prop) : (term898 A s) = (term898 A s).
Proof. exact (MK_COMB (@lem5822525 A) (@lem5822524 A s)). Qed.
Lemma lem5822527 {A : Type'} : (term899 A) = (term899 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5822526 A s)). Qed.
Lemma lem5822528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5822529 {A : Type'} : (term900 A) = (term900 A).
Proof. exact (MK_COMB (@lem5822528 A) (@lem5822527 A)). Qed.
Lemma lem5822530 {A : Type'} : (term600 A) = (term900 A).
Proof. exact (TRANS (@lem5822516 A) (@lem5822529 A)). Qed.
Lemma lem5822531 {A : Type'} (h1 : term7 A) : term900 A.
Proof. exact (EQ_MP (@lem5822530 A) (@lem5820975 A h1)). Qed.
Lemma lem5822754 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term567 A s x y) = (term901 A s x y).
Proof. exact (@lem19490 (term548 A x s) (term564 A x s y) (term279 A x y)). Qed.
Lemma lem5822755 {A : Type'} (s : A -> Prop) (x : A) : (term568 A s x) = (term902 A s x).
Proof. exact (fun_ext (fun y : A => @lem5822754 A s x y)). Qed.
Lemma lem5822756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822757 {A : Type'} (s : A -> Prop) (x : A) : (term569 A s x) = (term903 A s x).
Proof. exact (MK_COMB (@lem5822756 A) (@lem5822755 A s x)). Qed.
Lemma lem5822758 {A : Type'} (s : A -> Prop) : (term570 A s) = (term904 A s).
Proof. exact (fun_ext (fun x : A => @lem5822757 A s x)). Qed.
Lemma lem5822759 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5822760 {A : Type'} (s : A -> Prop) : (term571 A s) = (term905 A s).
Proof. exact (MK_COMB (@lem5822759 A) (@lem5822758 A s)). Qed.
Lemma lem5822761 {A : Type'} : (term572 A) = (term906 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5822760 A s)). Qed.
Lemma lem5822762 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5822764 {A : Type'} : (term573 A) = (term907 A).
Proof. exact (MK_COMB (@lem5822762 A) (@lem5822761 A)). Qed.
Lemma lem5822765 {A : Type'} (h1 : term8 A) : term907 A.
Proof. exact (EQ_MP (@lem5822764 A) (@lem5820980 A h1)). Qed.
Lemma lem5822886 {A : Type'} (_73522 : A) (h1 : term9 A) : term908 A _73522.
Proof. exact (@lem5821033 A h1 _73522). Qed.
Lemma lem5822887 {A : Type'} (_73522 : A) : (term908 A _73522) = (term554 A _73522).
Proof. exact (eq_refl (term908 A _73522)). Qed.
Lemma lem5822888 {A : Type'} (_73522 : A) (h1 : term9 A) : term554 A _73522.
Proof. exact (EQ_MP (@lem5822887 A _73522) (@lem5822886 A _73522 h1)). Qed.
Lemma lem5822889 {A : Type'} (_73522 : A) (_73523 : A -> Prop) (h1 : term9 A) : term909 A _73522 _73523.
Proof. exact (@lem5822888 A _73522 h1 _73523). Qed.
Lemma lem5822890 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term909 A _73522 _73523) = (term552 A _73522 _73523).
Proof. exact (eq_refl (term909 A _73522 _73523)). Qed.
Lemma lem5822928 {_120477 A B : Type'} (_73536 : type1400 B) (h1 : term99 _120477 A B) : term910 _120477 A B _73536.
Proof. exact (@lem5822117 _120477 A B h1 _73536). Qed.
Lemma lem5822929 {_120477 A B : Type'} (_73536 : type1400 B) : (term910 _120477 A B _73536) = (term881 _120477 A B _73536).
Proof. exact (eq_refl (term910 _120477 A B _73536)). Qed.
Lemma lem5822930 {_120477 A B : Type'} (_73536 : type1400 B) (h1 : term99 _120477 A B) : term881 _120477 A B _73536.
Proof. exact (EQ_MP (@lem5822929 _120477 A B _73536) (@lem5822928 _120477 A B _73536 h1)). Qed.
Lemma lem5822931 {_120477 A B : Type'} (_73536 : type1400 B) (_73537 : _120477 -> B) (h1 : term99 _120477 A B) : term911 _120477 A B _73536 _73537.
Proof. exact (@lem5822930 _120477 A B _73536 h1 _73537). Qed.
Lemma lem5822932 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73536 : type1400 B) : (term911 _120477 A B _73536 _73537) = (term879 _120477 A B _73537 _73536).
Proof. exact (eq_refl (term911 _120477 A B _73536 _73537)). Qed.
Lemma lem5822933 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73536 : type1400 B) (h1 : term99 _120477 A B) : term879 _120477 A B _73537 _73536.
Proof. exact (EQ_MP (@lem5822932 _120477 A B _73537 _73536) (@lem5822931 _120477 A B _73536 _73537 h1)). Qed.
Lemma lem5822934 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73536 : type1400 B) (_73538 : A -> B) (h1 : term99 _120477 A B) : term912 _120477 A B _73537 _73536 _73538.
Proof. exact (@lem5822933 _120477 A B _73537 _73536 h1 _73538). Qed.
Lemma lem5822935 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73536 : type1400 B) (_73538 : A -> B) : (term912 _120477 A B _73537 _73536 _73538) = (term877 _120477 A B _73537 _73536 _73538).
Proof. exact (eq_refl (term912 _120477 A B _73537 _73536 _73538)). Qed.
Lemma lem5822936 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73536 : type1400 B) (_73538 : A -> B) (h1 : term99 _120477 A B) : term877 _120477 A B _73537 _73536 _73538.
Proof. exact (EQ_MP (@lem5822935 _120477 A B _73537 _73536 _73538) (@lem5822934 _120477 A B _73537 _73536 _73538 h1)). Qed.
Lemma lem5822937 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73536 : type1400 B) (_73538 : A -> B) (_73539 : A) (h1 : term99 _120477 A B) : term913 _120477 A B _73537 _73536 _73538 _73539.
Proof. exact (@lem5822936 _120477 A B _73537 _73536 _73538 h1 _73539). Qed.
Lemma lem5822938 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73539 : A) (_73536 : type1400 B) (_73538 : A -> B) : (term913 _120477 A B _73537 _73536 _73538 _73539) = (term875 _120477 A B _73537 _73539 _73536 _73538).
Proof. exact (eq_refl (term913 _120477 A B _73537 _73536 _73538 _73539)). Qed.
Lemma lem5822939 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73539 : A) (_73536 : type1400 B) (_73538 : A -> B) (h1 : term99 _120477 A B) : term875 _120477 A B _73537 _73539 _73536 _73538.
Proof. exact (EQ_MP (@lem5822938 _120477 A B _73537 _73539 _73536 _73538) (@lem5822937 _120477 A B _73537 _73536 _73538 _73539 h1)). Qed.
Lemma lem5822940 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73539 : A) (_73536 : type1400 B) (_73538 : A -> B) (_73540 : A -> Prop) (h1 : term99 _120477 A B) : term914 _120477 A B _73537 _73539 _73536 _73538 _73540.
Proof. exact (@lem5822939 _120477 A B _73537 _73539 _73536 _73538 h1 _73540). Qed.
Lemma lem5822941 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term914 _120477 A B _73537 _73539 _73536 _73538 _73540) = (term873 _120477 A B _73537 _73539 _73536 _73540 _73538).
Proof. exact (eq_refl (term914 _120477 A B _73537 _73539 _73536 _73538 _73540)). Qed.
Lemma lem5822942 {_120477 A B : Type'} (_73537 : _120477 -> B) (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) (h1 : term99 _120477 A B) : term873 _120477 A B _73537 _73539 _73536 _73540 _73538.
Proof. exact (EQ_MP (@lem5822941 _120477 A B _73537 _73539 _73536 _73540 _73538) (@lem5822940 _120477 A B _73537 _73539 _73536 _73538 _73540 h1)). Qed.
Lemma lem5822958 {A : Type'} (_73546 : A -> Prop) (h1 : term7 A) : term915 A _73546.
Proof. exact (@lem5822531 A h1 _73546). Qed.
Lemma lem5822959 {A : Type'} (_73546 : A -> Prop) : (term915 A _73546) = (term898 A _73546).
Proof. exact (eq_refl (term915 A _73546)). Qed.
Lemma lem5822960 {A : Type'} (_73546 : A -> Prop) (h1 : term7 A) : term898 A _73546.
Proof. exact (EQ_MP (@lem5822959 A _73546) (@lem5822958 A _73546 h1)). Qed.
Lemma lem5822961 {A : Type'} (_73546 : A -> Prop) (_73547 : A) (h1 : term7 A) : term916 A _73546 _73547.
Proof. exact (@lem5822960 A _73546 h1 _73547). Qed.
Lemma lem5822962 {A : Type'} (_73547 : A) (_73546 : A -> Prop) : (term916 A _73546 _73547) = (term895 A _73547 _73546).
Proof. exact (eq_refl (term916 A _73546 _73547)). Qed.
Lemma lem5823009 {A : Type'} (_73563 : A -> Prop) (h1 : term8 A) : term917 A _73563.
Proof. exact (@lem5822765 A h1 _73563). Qed.
Lemma lem5823010 {A : Type'} (_73563 : A -> Prop) : (term917 A _73563) = (term905 A _73563).
Proof. exact (eq_refl (term917 A _73563)). Qed.
Lemma lem5823011 {A : Type'} (_73563 : A -> Prop) (h1 : term8 A) : term905 A _73563.
Proof. exact (EQ_MP (@lem5823010 A _73563) (@lem5823009 A _73563 h1)). Qed.
Lemma lem5823012 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (h1 : term8 A) : term918 A _73563 _73564.
Proof. exact (@lem5823011 A _73563 h1 _73564). Qed.
Lemma lem5823013 {A : Type'} (_73563 : A -> Prop) (_73564 : A) : (term918 A _73563 _73564) = (term903 A _73563 _73564).
Proof. exact (eq_refl (term918 A _73563 _73564)). Qed.
Lemma lem5823014 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (h1 : term8 A) : term903 A _73563 _73564.
Proof. exact (EQ_MP (@lem5823013 A _73563 _73564) (@lem5823012 A _73563 _73564 h1)). Qed.
Lemma lem5823015 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) (h1 : term8 A) : term919 A _73563 _73564 _73565.
Proof. exact (@lem5823014 A _73563 _73564 h1 _73565). Qed.
Lemma lem5823016 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) : (term919 A _73563 _73564 _73565) = (term901 A _73563 _73564 _73565).
Proof. exact (eq_refl (term919 A _73563 _73564 _73565)). Qed.
Lemma lem5823017 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) (h1 : term8 A) : term901 A _73563 _73564 _73565.
Proof. exact (EQ_MP (@lem5823016 A _73563 _73564 _73565) (@lem5823015 A _73563 _73564 _73565 h1)). Qed.
Lemma lem5823066 {_120477 A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) (h1 : term99 _120477 A B) : term871 A B _73539 _73536 _73540 _73538.
Proof. exact (proj2 (@lem5822942 _120477 A B (@el (_120477 -> B)) _73539 _73536 _73540 _73538 h1)). Qed.
Lemma lem5823095 {A : Type'} (_73522 : A) (_73523 : A -> Prop) (h1 : term9 A) : term552 A _73522 _73523.
Proof. exact (EQ_MP (@lem5822890 A _73522 _73523) (@lem5822889 A _73522 _73523 h1)). Qed.
Lemma lem5823115 {A : Type'} (_73547 : A) (_73546 : A -> Prop) (h1 : term7 A) : term895 A _73547 _73546.
Proof. exact (EQ_MP (@lem5822962 A _73547 _73546) (@lem5822961 A _73546 _73547 h1)). Qed.
Lemma lem5823209 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) (h1 : term8 A) : term920 A _73563 _73564 _73565.
Proof. exact (proj2 (@lem5823017 A _73563 _73564 _73565 h1)). Qed.
Lemma lem5823289 {_120477 A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) (h1 : term99 _120477 A B) : term921 A B _73539 _73536 _73540 _73538.
Proof. exact (proj2 (@lem5823066 _120477 A B _73539 _73536 _73540 _73538 h1)). Qed.
Lemma lem5823802 {A B : Type'} : (@I ((A -> Prop) -> (A -> B) -> B)) = (@I ((A -> Prop) -> (A -> B) -> B)).
Proof. exact (eq_refl (@I ((A -> Prop) -> (A -> B) -> B))). Qed.
Lemma lem5823803 {A B : Type'} (_73690 : type632 A B) (_73692 : type632 A B) (h1 : _73690 = _73692) : _73690 = _73692.
Proof. exact (h1). Qed.
Lemma lem5823804 {A : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (h1 : _73691 = _73693) : _73691 = _73693.
Proof. exact (h1). Qed.
Lemma lem5823805 {A B : Type'} (_73690 : type632 A B) (_73692 : type632 A B) (h1 : _73690 = _73692) : (@I ((A -> Prop) -> (A -> B) -> B) _73690) = (@I ((A -> Prop) -> (A -> B) -> B) _73692).
Proof. exact (MK_COMB (@lem5823802 A B) (@lem5823803 A B _73690 _73692 h1)). Qed.
Lemma lem5823806 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) (h1 : _73691 = _73693) (h2 : _73690 = _73692) : (@I ((A -> Prop) -> (A -> B) -> B) _73690 _73691) = (@I ((A -> Prop) -> (A -> B) -> B) _73692 _73693).
Proof. exact (MK_COMB (@lem5823805 A B _73690 _73692 h2) (@lem5823804 A _73691 _73693 h1)). Qed.
Lemma lem5823807 {A B : Type'} (_73690 : type632 A B) (_73692 : type632 A B) (_73691 : A -> Prop) (_73693 : A -> Prop) (h1 : _73691 = _73693) : term922 A B _73690 _73691 _73692 _73693.
Proof. exact (fun h0 : _73690 = _73692 => @lem5823806 A B _73691 _73693 _73690 _73692 h1 h0). Qed.
Lemma lem5823809 (a : Prop) (b : Prop) : (a -> b) = (term923 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5823810 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : (term922 A B _73690 _73691 _73692 _73693) = (term924 A B _73690 _73691 _73692 _73693).
Proof. exact (@lem5823809 (_73690 = _73692) ((@I ((A -> Prop) -> (A -> B) -> B) _73690 _73691) = (@I ((A -> Prop) -> (A -> B) -> B) _73692 _73693))). Qed.
Lemma lem5823811 {A B : Type'} (_73690 : type632 A B) (_73692 : type632 A B) (_73691 : A -> Prop) (_73693 : A -> Prop) (h1 : _73691 = _73693) : term924 A B _73690 _73691 _73692 _73693.
Proof. exact (EQ_MP (@lem5823810 A B _73690 _73691 _73692 _73693) (@lem5823807 A B _73690 _73692 _73691 _73693 h1)). Qed.
Lemma lem5823812 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : term925 A B _73690 _73691 _73692 _73693.
Proof. exact (fun h0 : _73691 = _73693 => @lem5823811 A B _73690 _73692 _73691 _73693 h0). Qed.
Lemma lem5823814 (a : Prop) (b : Prop) : (a -> b) = (term923 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5823815 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : (term925 A B _73690 _73691 _73692 _73693) = (term926 A B _73690 _73691 _73692 _73693).
Proof. exact (@lem5823814 (_73691 = _73693) (term924 A B _73690 _73691 _73692 _73693)). Qed.
Lemma lem5823816 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : term926 A B _73690 _73691 _73692 _73693.
Proof. exact (EQ_MP (@lem5823815 A B _73690 _73691 _73692 _73693) (@lem5823812 A B _73690 _73691 _73692 _73693)). Qed.
Lemma lem5823817 {A B : Type'} : (@I ((A -> B) -> B)) = (@I ((A -> B) -> B)).
Proof. exact (eq_refl (@I ((A -> B) -> B))). Qed.
Lemma lem5823818 {A B : Type'} (_73694 : type570 A B) (_73696 : type570 A B) (h1 : _73694 = _73696) : _73694 = _73696.
Proof. exact (h1). Qed.
Lemma lem5823819 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (h1 : _73695 = _73697) : _73695 = _73697.
Proof. exact (h1). Qed.
Lemma lem5823820 {A B : Type'} (_73694 : type570 A B) (_73696 : type570 A B) (h1 : _73694 = _73696) : (@I ((A -> B) -> B) _73694) = (@I ((A -> B) -> B) _73696).
Proof. exact (MK_COMB (@lem5823817 A B) (@lem5823818 A B _73694 _73696 h1)). Qed.
Lemma lem5823821 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) (h1 : _73695 = _73697) (h2 : _73694 = _73696) : (@I ((A -> B) -> B) _73694 _73695) = (@I ((A -> B) -> B) _73696 _73697).
Proof. exact (MK_COMB (@lem5823820 A B _73694 _73696 h2) (@lem5823819 A B _73695 _73697 h1)). Qed.
Lemma lem5823822 {A B : Type'} (_73694 : type570 A B) (_73696 : type570 A B) (_73695 : A -> B) (_73697 : A -> B) (h1 : _73695 = _73697) : term927 A B _73694 _73695 _73696 _73697.
Proof. exact (fun h0 : _73694 = _73696 => @lem5823821 A B _73695 _73697 _73694 _73696 h1 h0). Qed.
Lemma lem5823824 (a : Prop) (b : Prop) : (a -> b) = (term923 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5823825 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : (term927 A B _73694 _73695 _73696 _73697) = (term928 A B _73694 _73695 _73696 _73697).
Proof. exact (@lem5823824 (_73694 = _73696) ((@I ((A -> B) -> B) _73694 _73695) = (@I ((A -> B) -> B) _73696 _73697))). Qed.
Lemma lem5823826 {A B : Type'} (_73694 : type570 A B) (_73696 : type570 A B) (_73695 : A -> B) (_73697 : A -> B) (h1 : _73695 = _73697) : term928 A B _73694 _73695 _73696 _73697.
Proof. exact (EQ_MP (@lem5823825 A B _73694 _73695 _73696 _73697) (@lem5823822 A B _73694 _73696 _73695 _73697 h1)). Qed.
Lemma lem5823827 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : term929 A B _73694 _73695 _73696 _73697.
Proof. exact (fun h0 : _73695 = _73697 => @lem5823826 A B _73694 _73696 _73695 _73697 h0). Qed.
Lemma lem5823829 (a : Prop) (b : Prop) : (a -> b) = (term923 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5823830 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : (term929 A B _73694 _73695 _73696 _73697) = (term930 A B _73694 _73695 _73696 _73697).
Proof. exact (@lem5823829 (_73695 = _73697) (term928 A B _73694 _73695 _73696 _73697)). Qed.
Lemma lem5823831 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : term930 A B _73694 _73695 _73696 _73697.
Proof. exact (EQ_MP (@lem5823830 A B _73694 _73695 _73696 _73697) (@lem5823827 A B _73694 _73695 _73696 _73697)). Qed.
Lemma lem5824187 {B : Type'} (x : B) (y : B) (z : B) : term931 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5824255 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (proj1 (@lem5820967 A B a op s f h1)). Qed.
Lemma lem5824256 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term932 B op.
Proof. exact (fun h0 : term652 B op => @lem5824255 A B a op s f h1). Qed.
Lemma lem5824258 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824259 {B : Type'} (op : type1400 B) : (term932 B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5824258 (@I ((B -> B -> B) -> Prop) (@monoidal B) op)). Qed.
Lemma lem5824260 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (EQ_MP (@lem5824259 B op) (@lem5824256 A B a op s f h1)). Qed.
Lemma lem5824262 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem5820971 A B a op s f h1)). Qed.
Lemma lem5824263 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term934 A s.
Proof. exact (fun h0 : term594 A s => @lem5824262 A B a op s f h1). Qed.
Lemma lem5824265 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824266 {A : Type'} (s : A -> Prop) : (term934 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5824265 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem5824267 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem5824266 A s) (@lem5824263 A B a op s f h1)). Qed.
Lemma lem5824269 (b : Prop) (a : Prop) : (a \/ b) = (term935 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5824270 {A : Type'} (_73546 : A -> Prop) (_73547 : A) : (term895 A _73547 _73546) = (term936 A _73546 _73547).
Proof. exact (@lem5824269 (term594 A _73546) (term586 A _73546 _73547)). Qed.
Lemma lem5824272 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824273 {A : Type'} (_73546 : A -> Prop) : (term938 A _73546) = (@I ((A -> Prop) -> Prop) (@FINITE A) _73546).
Proof. exact (@lem5824272 (@I ((A -> Prop) -> Prop) (@FINITE A) _73546)). Qed.
Lemma lem5824274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5824275 {A : Type'} (_73546 : A -> Prop) : (term939 A _73546) = (term940 A _73546).
Proof. exact (MK_COMB (@lem5824274) (@lem5824273 A _73546)). Qed.
Lemma lem5824276 {A : Type'} (_73546 : A -> Prop) (_73547 : A) : (term586 A _73546 _73547) = (term586 A _73546 _73547).
Proof. exact (eq_refl (term586 A _73546 _73547)). Qed.
Lemma lem5824277 {A : Type'} (_73546 : A -> Prop) (_73547 : A) : (term936 A _73546 _73547) = (term941 A _73546 _73547).
Proof. exact (MK_COMB (@lem5824275 A _73546) (@lem5824276 A _73546 _73547)). Qed.
Lemma lem5824278 {A : Type'} (_73546 : A -> Prop) (_73547 : A) : (term895 A _73547 _73546) = (term941 A _73546 _73547).
Proof. exact (TRANS (@lem5824270 A _73546 _73547) (@lem5824277 A _73546 _73547)). Qed.
Lemma lem5824281 {A : Type'} (_73546 : A -> Prop) (_73547 : A) (h1 : term7 A) : term941 A _73546 _73547.
Proof. exact (EQ_MP (@lem5824278 A _73546 _73547) (@lem5823115 A _73547 _73546 h1)). Qed.
Lemma lem5824282 {A : Type'} (_73546 : A -> Prop) (_73547 : A) (h1 : term7 A) : term941 A _73546 _73547.
Proof. exact (@lem5824281 A _73546 _73547 h1). Qed.
Lemma lem5824283 {A : Type'} (s : A -> Prop) (_73547 : A) (h1 : term7 A) : term941 A s _73547.
Proof. exact (@lem5824282 A s _73547 h1). Qed.
Lemma lem5824286 {A B : Type'} (_73547 : A) (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term7 A) (h2 : term258 A B a op s f) : term586 A s _73547.
Proof. exact (@lem5824283 A s _73547 h1 (@lem5824267 A B a op s f h2)). Qed.
Lemma lem5824287 {A B : Type'} (_73547 : A) (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term7 A) (h2 : term258 A B a op s f) : term586 A s _73547.
Proof. exact (@lem5824286 A B _73547 a op s f h1 h2). Qed.
Lemma lem5824288 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term7 A) (h2 : term258 A B a op s f) : term586 A s a.
Proof. exact (@lem5824287 A B a a op s f h1 h2). Qed.
Lemma lem5824289 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term7 A) (h2 : term258 A B a op s f) : term942 A s a.
Proof. exact (fun h0 : term587 A s a => @lem5824288 A B a op s f h1 h2). Qed.
Lemma lem5824291 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824292 {A : Type'} (s : A -> Prop) (a : A) : (term942 A s a) = (term586 A s a).
Proof. exact (@lem5824291 (term586 A s a)). Qed.
Lemma lem5824293 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term7 A) (h2 : term258 A B a op s f) : term586 A s a.
Proof. exact (EQ_MP (@lem5824292 A s a) (@lem5824289 A B a op s f h1 h2)). Qed.
Lemma lem5824295 {A B : Type'} (x : A -> B) : x = x.
Proof. exact (@lem21386 (A -> B) x). Qed.
Lemma lem5824296 {A B : Type'} (x : A -> B) : x = x.
Proof. exact (@lem5824295 A B x). Qed.
Lemma lem5824297 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (@lem5824296 A B f). Qed.
Lemma lem5824298 {A B : Type'} (f : A -> B) : term943 A B f.
Proof. exact (fun h0 : term944 A B f => @lem5824297 A B f). Qed.
Lemma lem5824300 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824301 {A B : Type'} (f : A -> B) : (term943 A B f) = (f = f).
Proof. exact (@lem5824300 (f = f)). Qed.
Lemma lem5824302 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (EQ_MP (@lem5824301 A B f) (@lem5824298 A B f)). Qed.
Lemma lem5824304 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term548 A a s.
Proof. exact (proj2 (@lem5820971 A B a op s f h1)). Qed.
Lemma lem5824305 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term945 A a s.
Proof. exact (fun h0 : term550 A a s => @lem5824304 A B a op s f h1). Qed.
Lemma lem5824307 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824308 {A : Type'} (a : A) (s : A -> Prop) : (term945 A a s) = (term548 A a s).
Proof. exact (@lem5824307 (term548 A a s)). Qed.
Lemma lem5824309 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term548 A a s.
Proof. exact (EQ_MP (@lem5824308 A a s) (@lem5824305 A B a op s f h1)). Qed.
Lemma lem5824315 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5824316 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term552 A _73522 _73523) = (term946 A _73522 _73523).
Proof. exact (@lem5824315 ((term545 A _73523 _73522) = _73523) (term550 A _73522 _73523)). Qed.
Lemma lem5824324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5824325 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term947 A _73522 _73523) = (term948 A _73522 _73523).
Proof. exact (MK_COMB (@lem5824324) (@lem5824316 A _73522 _73523)). Qed.
Lemma lem5824333 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term946 A _73522 _73523) = (term946 A _73522 _73523).
Proof. exact (eq_refl (term946 A _73522 _73523)). Qed.
Lemma lem5824334 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : ((term552 A _73522 _73523) = (term946 A _73522 _73523)) = ((term946 A _73522 _73523) = (term946 A _73522 _73523)).
Proof. exact (MK_COMB (@lem5824325 A _73522 _73523) (@lem5824333 A _73522 _73523)). Qed.
Lemma lem5824336 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5824337 (x : Prop) : (x = x) = True.
Proof. exact (@lem5824336 Prop x). Qed.
Lemma lem5824338 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : ((term946 A _73522 _73523) = (term946 A _73522 _73523)) = True.
Proof. exact (@lem5824337 (term946 A _73522 _73523)). Qed.
Lemma lem5824339 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : ((term552 A _73522 _73523) = (term946 A _73522 _73523)) = True.
Proof. exact (TRANS (@lem5824334 A _73522 _73523) (@lem5824338 A _73522 _73523)). Qed.
Lemma lem5824340 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : True = ((term552 A _73522 _73523) = (term946 A _73522 _73523)).
Proof. exact (SYM (@lem5824339 A _73522 _73523)). Qed.
Lemma lem5824341 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term552 A _73522 _73523) = (term946 A _73522 _73523).
Proof. exact (EQ_MP (@lem5824340 A _73522 _73523) (@lem0)). Qed.
Lemma lem5824342 {A : Type'} (_73522 : A) (_73523 : A -> Prop) (h1 : term9 A) : term946 A _73522 _73523.
Proof. exact (EQ_MP (@lem5824341 A _73522 _73523) (@lem5823095 A _73522 _73523 h1)). Qed.
Lemma lem5824344 (b : Prop) (a : Prop) : (a \/ b) = (term935 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5824345 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term946 A _73522 _73523) = (term949 A _73522 _73523).
Proof. exact (@lem5824344 (term550 A _73522 _73523) ((term545 A _73523 _73522) = _73523)). Qed.
Lemma lem5824347 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824348 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term950 A _73522 _73523) = (term548 A _73522 _73523).
Proof. exact (@lem5824347 (term548 A _73522 _73523)). Qed.
Lemma lem5824349 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5824350 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term951 A _73522 _73523) = (term952 A _73522 _73523).
Proof. exact (MK_COMB (@lem5824349) (@lem5824348 A _73522 _73523)). Qed.
Lemma lem5824351 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : ((term545 A _73523 _73522) = _73523) = ((term545 A _73523 _73522) = _73523).
Proof. exact (eq_refl ((term545 A _73523 _73522) = _73523)). Qed.
Lemma lem5824352 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term949 A _73522 _73523) = (term953 A _73522 _73523).
Proof. exact (MK_COMB (@lem5824350 A _73522 _73523) (@lem5824351 A _73522 _73523)). Qed.
Lemma lem5824353 {A : Type'} (_73522 : A) (_73523 : A -> Prop) : (term946 A _73522 _73523) = (term953 A _73522 _73523).
Proof. exact (TRANS (@lem5824345 A _73522 _73523) (@lem5824352 A _73522 _73523)). Qed.
Lemma lem5824356 {A : Type'} (_73522 : A) (_73523 : A -> Prop) (h1 : term9 A) : term953 A _73522 _73523.
Proof. exact (EQ_MP (@lem5824353 A _73522 _73523) (@lem5824342 A _73522 _73523 h1)). Qed.
Lemma lem5824357 {A : Type'} (_73522 : A) (_73523 : A -> Prop) (h1 : term9 A) : term953 A _73522 _73523.
Proof. exact (@lem5824356 A _73522 _73523 h1). Qed.
Lemma lem5824358 {A : Type'} (a : A) (s : A -> Prop) (h1 : term9 A) : term953 A a s.
Proof. exact (@lem5824357 A a s h1). Qed.
Lemma lem5824361 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : (term545 A s a) = s.
Proof. exact (@lem5824358 A a s h1 (@lem5824309 A B a op s f h2)). Qed.
Lemma lem5824362 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term954 A a s.
Proof. exact (fun h0 : term955 A a s => @lem5824361 A B a op s f h1 h2). Qed.
Lemma lem5824364 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824365 {A : Type'} (a : A) (s : A -> Prop) : (term954 A a s) = ((term545 A s a) = s).
Proof. exact (@lem5824364 ((term545 A s a) = s)). Qed.
Lemma lem5824366 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : (term545 A s a) = s.
Proof. exact (EQ_MP (@lem5824365 A a s) (@lem5824362 A B a op s f h1 h2)). Qed.
Lemma lem5824368 {A B : Type'} (x : type632 A B) : x = x.
Proof. exact (@lem21386 (type632 A B) x). Qed.
Lemma lem5824369 {A B : Type'} (x : type632 A B) : x = x.
Proof. exact (@lem5824368 A B x). Qed.
Lemma lem5824370 {A B : Type'} (op : type1400 B) : (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (@lem5824369 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op)). Qed.
Lemma lem5824371 {A B : Type'} (op : type1400 B) : term956 A B op.
Proof. exact (fun h0 : term957 A B op => @lem5824370 A B op). Qed.
Lemma lem5824373 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824374 {A B : Type'} (op : type1400 B) : (term956 A B op) = ((@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op)).
Proof. exact (@lem5824373 ((@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op))). Qed.
Lemma lem5824375 {A B : Type'} (op : type1400 B) : (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) = (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op).
Proof. exact (EQ_MP (@lem5824374 A B op) (@lem5824371 A B op)). Qed.
Lemma lem5824393 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5824394 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term924 A B _73690 _73691 _73692 _73693) = (term958 A B _73691 _73693 _73690 _73692).
Proof. exact (@lem5824393 ((@I ((A -> Prop) -> (A -> B) -> B) _73690 _73691) = (@I ((A -> Prop) -> (A -> B) -> B) _73692 _73693)) (term959 A B _73690 _73692)). Qed.
Lemma lem5824404 {A : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) : (term960 A _73691 _73693) = (term960 A _73691 _73693).
Proof. exact (eq_refl (term960 A _73691 _73693)). Qed.
Lemma lem5824405 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term926 A B _73690 _73691 _73692 _73693) = (term961 A B _73691 _73693 _73690 _73692).
Proof. exact (MK_COMB (@lem5824404 A _73691 _73693) (@lem5824394 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824409 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824410 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term961 A B _73691 _73693 _73690 _73692) = (term963 A B _73691 _73693 _73690 _73692).
Proof. exact (@lem5824409 ((@I ((A -> Prop) -> (A -> B) -> B) _73690 _73691) = (@I ((A -> Prop) -> (A -> B) -> B) _73692 _73693)) (term964 A _73691 _73693) (term959 A B _73690 _73692)). Qed.
Lemma lem5824432 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term926 A B _73690 _73691 _73692 _73693) = (term963 A B _73691 _73693 _73690 _73692).
Proof. exact (TRANS (@lem5824405 A B _73691 _73693 _73690 _73692) (@lem5824410 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5824434 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term965 A B _73690 _73691 _73692 _73693) = (term966 A B _73691 _73693 _73690 _73692).
Proof. exact (MK_COMB (@lem5824433) (@lem5824432 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824456 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term963 A B _73691 _73693 _73690 _73692) = (term963 A B _73691 _73693 _73690 _73692).
Proof. exact (eq_refl (term963 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824457 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : ((term926 A B _73690 _73691 _73692 _73693) = (term963 A B _73691 _73693 _73690 _73692)) = ((term963 A B _73691 _73693 _73690 _73692) = (term963 A B _73691 _73693 _73690 _73692)).
Proof. exact (MK_COMB (@lem5824434 A B _73691 _73693 _73690 _73692) (@lem5824456 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824459 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5824460 (x : Prop) : (x = x) = True.
Proof. exact (@lem5824459 Prop x). Qed.
Lemma lem5824461 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : ((term963 A B _73691 _73693 _73690 _73692) = (term963 A B _73691 _73693 _73690 _73692)) = True.
Proof. exact (@lem5824460 (term963 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824462 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : ((term926 A B _73690 _73691 _73692 _73693) = (term963 A B _73691 _73693 _73690 _73692)) = True.
Proof. exact (TRANS (@lem5824457 A B _73691 _73693 _73690 _73692) (@lem5824461 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824463 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : True = ((term926 A B _73690 _73691 _73692 _73693) = (term963 A B _73691 _73693 _73690 _73692)).
Proof. exact (SYM (@lem5824462 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824464 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term926 A B _73690 _73691 _73692 _73693) = (term963 A B _73691 _73693 _73690 _73692).
Proof. exact (EQ_MP (@lem5824463 A B _73691 _73693 _73690 _73692) (@lem0)). Qed.
Lemma lem5824465 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : term963 A B _73691 _73693 _73690 _73692.
Proof. exact (EQ_MP (@lem5824464 A B _73691 _73693 _73690 _73692) (@lem5823816 A B _73690 _73691 _73692 _73693)). Qed.
Lemma lem5824467 (b : Prop) (a : Prop) : (a \/ b) = (term935 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5824468 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : (term963 A B _73691 _73693 _73690 _73692) = (term967 A B _73690 _73691 _73692 _73693).
Proof. exact (@lem5824467 (term968 A B _73691 _73693 _73690 _73692) ((@I ((A -> Prop) -> (A -> B) -> B) _73690 _73691) = (@I ((A -> Prop) -> (A -> B) -> B) _73692 _73693))). Qed.
Lemma lem5824470 (a : Prop) (b : Prop) : (term969 a b) = (term970 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5824471 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term971 A B _73691 _73693 _73690 _73692) = (term972 A B _73691 _73693 _73690 _73692).
Proof. exact (@lem5824470 (term964 A _73691 _73693) (term959 A B _73690 _73692)). Qed.
Lemma lem5824473 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824474 {A : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) : (term973 A _73691 _73693) = (_73691 = _73693).
Proof. exact (@lem5824473 (_73691 = _73693)). Qed.
Lemma lem5824475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5824476 {A : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) : (term974 A _73691 _73693) = (term975 A _73691 _73693).
Proof. exact (MK_COMB (@lem5824475) (@lem5824474 A _73691 _73693)). Qed.
Lemma lem5824478 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824479 {A B : Type'} (_73690 : type632 A B) (_73692 : type632 A B) : (term976 A B _73690 _73692) = (_73690 = _73692).
Proof. exact (@lem5824478 (_73690 = _73692)). Qed.
Lemma lem5824480 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term972 A B _73691 _73693 _73690 _73692) = (term977 A B _73691 _73693 _73690 _73692).
Proof. exact (MK_COMB (@lem5824476 A _73691 _73693) (@lem5824479 A B _73690 _73692)). Qed.
Lemma lem5824481 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term971 A B _73691 _73693 _73690 _73692) = (term977 A B _73691 _73693 _73690 _73692).
Proof. exact (TRANS (@lem5824471 A B _73691 _73693 _73690 _73692) (@lem5824480 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824482 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5824483 {A B : Type'} (_73691 : A -> Prop) (_73693 : A -> Prop) (_73690 : type632 A B) (_73692 : type632 A B) : (term978 A B _73691 _73693 _73690 _73692) = (term979 A B _73691 _73693 _73690 _73692).
Proof. exact (MK_COMB (@lem5824482) (@lem5824481 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824484 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : ((@I ((A -> Prop) -> (A -> B) -> B) _73690 _73691) = (@I ((A -> Prop) -> (A -> B) -> B) _73692 _73693)) = ((@I ((A -> Prop) -> (A -> B) -> B) _73690 _73691) = (@I ((A -> Prop) -> (A -> B) -> B) _73692 _73693)).
Proof. exact (eq_refl ((@I ((A -> Prop) -> (A -> B) -> B) _73690 _73691) = (@I ((A -> Prop) -> (A -> B) -> B) _73692 _73693))). Qed.
Lemma lem5824485 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : (term967 A B _73690 _73691 _73692 _73693) = (term980 A B _73690 _73691 _73692 _73693).
Proof. exact (MK_COMB (@lem5824483 A B _73691 _73693 _73690 _73692) (@lem5824484 A B _73690 _73691 _73692 _73693)). Qed.
Lemma lem5824486 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : (term963 A B _73691 _73693 _73690 _73692) = (term980 A B _73690 _73691 _73692 _73693).
Proof. exact (TRANS (@lem5824468 A B _73690 _73691 _73692 _73693) (@lem5824485 A B _73690 _73691 _73692 _73693)). Qed.
Lemma lem5824488 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term981 A B a s op.
Proof. exact (conj (@lem5824366 A B a op s f h1 h2) (@lem5824375 A B op)). Qed.
Lemma lem5824490 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : term980 A B _73690 _73691 _73692 _73693.
Proof. exact (EQ_MP (@lem5824486 A B _73690 _73691 _73692 _73693) (@lem5824465 A B _73691 _73693 _73690 _73692)). Qed.
Lemma lem5824491 {A B : Type'} (_73690 : type632 A B) (_73691 : A -> Prop) (_73692 : type632 A B) (_73693 : A -> Prop) : term980 A B _73690 _73691 _73692 _73693.
Proof. exact (@lem5824490 A B _73690 _73691 _73692 _73693). Qed.
Lemma lem5824492 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) : term982 A B a op s.
Proof. exact (@lem5824491 A B (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) (term545 A s a) (@I ((B -> B -> B) -> (A -> Prop) -> (A -> B) -> B) (@iterate B A) op) s). Qed.
Lemma lem5824495 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : (term983 A B op s a) = (term611 A B op s).
Proof. exact (@lem5824492 A B a op s (@lem5824488 A B a op s f h1 h2)). Qed.
Lemma lem5824496 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term984 A B a op s.
Proof. exact (fun h0 : term985 A B a op s => @lem5824495 A B a op s f h1 h2). Qed.
Lemma lem5824498 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824499 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) : (term984 A B a op s) = ((term983 A B op s a) = (term611 A B op s)).
Proof. exact (@lem5824498 ((term983 A B op s a) = (term611 A B op s))). Qed.
Lemma lem5824500 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : (term983 A B op s a) = (term611 A B op s).
Proof. exact (EQ_MP (@lem5824499 A B a op s) (@lem5824496 A B a op s f h1 h2)). Qed.
Lemma lem5824518 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5824519 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term928 A B _73694 _73695 _73696 _73697) = (term986 A B _73695 _73697 _73694 _73696).
Proof. exact (@lem5824518 ((@I ((A -> B) -> B) _73694 _73695) = (@I ((A -> B) -> B) _73696 _73697)) (term987 A B _73694 _73696)). Qed.
Lemma lem5824529 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) : (term988 A B _73695 _73697) = (term988 A B _73695 _73697).
Proof. exact (eq_refl (term988 A B _73695 _73697)). Qed.
Lemma lem5824530 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term930 A B _73694 _73695 _73696 _73697) = (term989 A B _73695 _73697 _73694 _73696).
Proof. exact (MK_COMB (@lem5824529 A B _73695 _73697) (@lem5824519 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824534 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824535 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term989 A B _73695 _73697 _73694 _73696) = (term990 A B _73695 _73697 _73694 _73696).
Proof. exact (@lem5824534 ((@I ((A -> B) -> B) _73694 _73695) = (@I ((A -> B) -> B) _73696 _73697)) (term991 A B _73695 _73697) (term987 A B _73694 _73696)). Qed.
Lemma lem5824557 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term930 A B _73694 _73695 _73696 _73697) = (term990 A B _73695 _73697 _73694 _73696).
Proof. exact (TRANS (@lem5824530 A B _73695 _73697 _73694 _73696) (@lem5824535 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5824559 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term992 A B _73694 _73695 _73696 _73697) = (term993 A B _73695 _73697 _73694 _73696).
Proof. exact (MK_COMB (@lem5824558) (@lem5824557 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824581 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term990 A B _73695 _73697 _73694 _73696) = (term990 A B _73695 _73697 _73694 _73696).
Proof. exact (eq_refl (term990 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824582 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : ((term930 A B _73694 _73695 _73696 _73697) = (term990 A B _73695 _73697 _73694 _73696)) = ((term990 A B _73695 _73697 _73694 _73696) = (term990 A B _73695 _73697 _73694 _73696)).
Proof. exact (MK_COMB (@lem5824559 A B _73695 _73697 _73694 _73696) (@lem5824581 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824584 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5824585 (x : Prop) : (x = x) = True.
Proof. exact (@lem5824584 Prop x). Qed.
Lemma lem5824586 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : ((term990 A B _73695 _73697 _73694 _73696) = (term990 A B _73695 _73697 _73694 _73696)) = True.
Proof. exact (@lem5824585 (term990 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824587 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : ((term930 A B _73694 _73695 _73696 _73697) = (term990 A B _73695 _73697 _73694 _73696)) = True.
Proof. exact (TRANS (@lem5824582 A B _73695 _73697 _73694 _73696) (@lem5824586 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824588 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : True = ((term930 A B _73694 _73695 _73696 _73697) = (term990 A B _73695 _73697 _73694 _73696)).
Proof. exact (SYM (@lem5824587 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824589 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term930 A B _73694 _73695 _73696 _73697) = (term990 A B _73695 _73697 _73694 _73696).
Proof. exact (EQ_MP (@lem5824588 A B _73695 _73697 _73694 _73696) (@lem0)). Qed.
Lemma lem5824590 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : term990 A B _73695 _73697 _73694 _73696.
Proof. exact (EQ_MP (@lem5824589 A B _73695 _73697 _73694 _73696) (@lem5823831 A B _73694 _73695 _73696 _73697)). Qed.
Lemma lem5824592 (b : Prop) (a : Prop) : (a \/ b) = (term935 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5824593 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : (term990 A B _73695 _73697 _73694 _73696) = (term994 A B _73694 _73695 _73696 _73697).
Proof. exact (@lem5824592 (term995 A B _73695 _73697 _73694 _73696) ((@I ((A -> B) -> B) _73694 _73695) = (@I ((A -> B) -> B) _73696 _73697))). Qed.
Lemma lem5824595 (a : Prop) (b : Prop) : (term969 a b) = (term970 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5824596 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term996 A B _73695 _73697 _73694 _73696) = (term997 A B _73695 _73697 _73694 _73696).
Proof. exact (@lem5824595 (term991 A B _73695 _73697) (term987 A B _73694 _73696)). Qed.
Lemma lem5824598 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824599 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) : (term998 A B _73695 _73697) = (_73695 = _73697).
Proof. exact (@lem5824598 (_73695 = _73697)). Qed.
Lemma lem5824600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5824601 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) : (term999 A B _73695 _73697) = (term1000 A B _73695 _73697).
Proof. exact (MK_COMB (@lem5824600) (@lem5824599 A B _73695 _73697)). Qed.
Lemma lem5824603 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824604 {A B : Type'} (_73694 : type570 A B) (_73696 : type570 A B) : (term1001 A B _73694 _73696) = (_73694 = _73696).
Proof. exact (@lem5824603 (_73694 = _73696)). Qed.
Lemma lem5824605 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term997 A B _73695 _73697 _73694 _73696) = (term1002 A B _73695 _73697 _73694 _73696).
Proof. exact (MK_COMB (@lem5824601 A B _73695 _73697) (@lem5824604 A B _73694 _73696)). Qed.
Lemma lem5824606 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term996 A B _73695 _73697 _73694 _73696) = (term1002 A B _73695 _73697 _73694 _73696).
Proof. exact (TRANS (@lem5824596 A B _73695 _73697 _73694 _73696) (@lem5824605 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5824608 {A B : Type'} (_73695 : A -> B) (_73697 : A -> B) (_73694 : type570 A B) (_73696 : type570 A B) : (term1003 A B _73695 _73697 _73694 _73696) = (term1004 A B _73695 _73697 _73694 _73696).
Proof. exact (MK_COMB (@lem5824607) (@lem5824606 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824609 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : ((@I ((A -> B) -> B) _73694 _73695) = (@I ((A -> B) -> B) _73696 _73697)) = ((@I ((A -> B) -> B) _73694 _73695) = (@I ((A -> B) -> B) _73696 _73697)).
Proof. exact (eq_refl ((@I ((A -> B) -> B) _73694 _73695) = (@I ((A -> B) -> B) _73696 _73697))). Qed.
Lemma lem5824610 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : (term994 A B _73694 _73695 _73696 _73697) = (term1005 A B _73694 _73695 _73696 _73697).
Proof. exact (MK_COMB (@lem5824608 A B _73695 _73697 _73694 _73696) (@lem5824609 A B _73694 _73695 _73696 _73697)). Qed.
Lemma lem5824611 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : (term990 A B _73695 _73697 _73694 _73696) = (term1005 A B _73694 _73695 _73696 _73697).
Proof. exact (TRANS (@lem5824593 A B _73694 _73695 _73696 _73697) (@lem5824610 A B _73694 _73695 _73696 _73697)). Qed.
Lemma lem5824613 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term1006 A B f a op s.
Proof. exact (conj (@lem5824302 A B f) (@lem5824500 A B a op s f h1 h2)). Qed.
Lemma lem5824615 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : term1005 A B _73694 _73695 _73696 _73697.
Proof. exact (EQ_MP (@lem5824611 A B _73694 _73695 _73696 _73697) (@lem5824590 A B _73695 _73697 _73694 _73696)). Qed.
Lemma lem5824616 {A B : Type'} (_73694 : type570 A B) (_73695 : A -> B) (_73696 : type570 A B) (_73697 : A -> B) : term1005 A B _73694 _73695 _73696 _73697.
Proof. exact (@lem5824615 A B _73694 _73695 _73696 _73697). Qed.
Lemma lem5824617 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term1007 A B a op s f.
Proof. exact (@lem5824616 A B (term983 A B op s a) f (term611 A B op s) f). Qed.
Lemma lem5824620 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : (term1008 A B op s a f) = (term613 A B op s f).
Proof. exact (@lem5824617 A B a op s f (@lem5824613 A B a op s f h1 h2)). Qed.
Lemma lem5824621 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term1009 A B a op s f.
Proof. exact (fun h0 : term1010 A B a op s f => @lem5824620 A B a op s f h1 h2). Qed.
Lemma lem5824623 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824624 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term1009 A B a op s f) = ((term1008 A B op s a f) = (term613 A B op s f)).
Proof. exact (@lem5824623 ((term1008 A B op s a f) = (term613 A B op s f))). Qed.
Lemma lem5824625 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : (term1008 A B op s a f) = (term613 A B op s f).
Proof. exact (EQ_MP (@lem5824624 A B a op s f) (@lem5824621 A B a op s f h1 h2)). Qed.
Lemma lem5824627 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term671 A B a op s f.
Proof. exact (proj2 (@lem5820968 A B a op s f h1)). Qed.
Lemma lem5824628 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term1011 A B a op s f.
Proof. exact (fun h0 : (term667 A B op s a f) = (term613 A B op s f) => @lem5824627 A B a op s f h1). Qed.
Lemma lem5824630 (p : Prop) : (term1012 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5824631 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term1011 A B a op s f) = (term671 A B a op s f).
Proof. exact (@lem5824630 ((term667 A B op s a f) = (term613 A B op s f))). Qed.
Lemma lem5824632 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term258 A B a op s f) : term671 A B a op s f.
Proof. exact (EQ_MP (@lem5824631 A B a op s f) (@lem5824628 A B a op s f h1)). Qed.
Lemma lem5824634 (b : Prop) (a : Prop) : (a \/ b) = (term935 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5824635 {B : Type'} (z : B) (x : B) (y : B) : (term931 B x y z) = (term1013 B z x y).
Proof. exact (@lem5824634 (term1014 B x y z) (term279 B x y)). Qed.
Lemma lem5824637 (a : Prop) (b : Prop) : (term969 a b) = (term970 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5824638 {B : Type'} (x : B) (y : B) (z : B) : (term1015 B x y z) = (term1016 B x y z).
Proof. exact (@lem5824637 (term279 B x z) (y = z)). Qed.
Lemma lem5824640 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824641 {B : Type'} (x : B) (z : B) : (term274 B x z) = (x = z).
Proof. exact (@lem5824640 (x = z)). Qed.
Lemma lem5824642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5824643 {B : Type'} (x : B) (z : B) : (term1017 B x z) = (term1018 B x z).
Proof. exact (MK_COMB (@lem5824642) (@lem5824641 B x z)). Qed.
Lemma lem5824644 {B : Type'} (y : B) (z : B) : (term279 B y z) = (term279 B y z).
Proof. exact (eq_refl (term279 B y z)). Qed.
Lemma lem5824645 {B : Type'} (x : B) (y : B) (z : B) : (term1016 B x y z) = (term1019 B x y z).
Proof. exact (MK_COMB (@lem5824643 B x z) (@lem5824644 B y z)). Qed.
Lemma lem5824646 {B : Type'} (x : B) (y : B) (z : B) : (term1015 B x y z) = (term1019 B x y z).
Proof. exact (TRANS (@lem5824638 B x y z) (@lem5824645 B x y z)). Qed.
Lemma lem5824647 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5824648 {B : Type'} (x : B) (y : B) (z : B) : (term1020 B x y z) = (term1021 B x y z).
Proof. exact (MK_COMB (@lem5824647) (@lem5824646 B x y z)). Qed.
Lemma lem5824649 {B : Type'} (x : B) (y : B) : (term279 B x y) = (term279 B x y).
Proof. exact (eq_refl (term279 B x y)). Qed.
Lemma lem5824650 {B : Type'} (z : B) (x : B) (y : B) : (term1013 B z x y) = (term1022 B z x y).
Proof. exact (MK_COMB (@lem5824648 B x y z) (@lem5824649 B x y)). Qed.
Lemma lem5824651 {B : Type'} (z : B) (x : B) (y : B) : (term931 B x y z) = (term1022 B z x y).
Proof. exact (TRANS (@lem5824635 B z x y) (@lem5824650 B z x y)). Qed.
Lemma lem5824653 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term1023 A B a op s f.
Proof. exact (conj (@lem5824625 A B a op s f h1 h2) (@lem5824632 A B a op s f h2)). Qed.
Lemma lem5824655 {B : Type'} (z : B) (x : B) (y : B) : term1022 B z x y.
Proof. exact (EQ_MP (@lem5824651 B z x y) (@lem5824187 B x y z)). Qed.
Lemma lem5824656 {B : Type'} (z : B) (x : B) (y : B) : term1022 B z x y.
Proof. exact (@lem5824655 B z x y). Qed.
Lemma lem5824657 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : term1024 A B op s a f.
Proof. exact (@lem5824656 B (term613 A B op s f) (term1008 A B op s a f) (term667 A B op s a f)). Qed.
Lemma lem5824660 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term1025 A B op s a f.
Proof. exact (@lem5824657 A B op s a f (@lem5824653 A B a op s f h1 h2)). Qed.
Lemma lem5824661 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term1026 A B op s a f.
Proof. exact (fun h0 : (term1008 A B op s a f) = (term667 A B op s a f) => @lem5824660 A B a op s f h1 h2). Qed.
Lemma lem5824663 (p : Prop) : (term1012 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5824664 {A B : Type'} (op : type1400 B) (s : A -> Prop) (a : A) (f : A -> B) : (term1026 A B op s a f) = (term1025 A B op s a f).
Proof. exact (@lem5824663 ((term1008 A B op s a f) = (term667 A B op s a f))). Qed.
Lemma lem5824665 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term258 A B a op s f) : term1025 A B op s a f.
Proof. exact (EQ_MP (@lem5824664 A B op s a f) (@lem5824661 A B a op s f h1 h2)). Qed.
Lemma lem5824671 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824672 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term921 A B _73539 _73536 _73540 _73538) = (term1027 A B _73539 _73536 _73540 _73538).
Proof. exact (@lem5824671 (term548 A _73539 _73540) (term652 B _73536) (term623 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824686 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824687 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1028 A B _73539 _73536 _73540 _73538) = (term1029 A B _73539 _73536 _73540 _73538).
Proof. exact (@lem5824686 (term594 A _73540) (term652 B _73536) ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538))). Qed.
Lemma lem5824701 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5824702 {A B : Type'} (_73539 : A) (_73540 : A -> Prop) (_73538 : A -> B) (_73536 : type1400 B) : (term1030 A B _73539 _73536 _73540 _73538) = (term1031 A B _73539 _73540 _73538 _73536).
Proof. exact (@lem5824701 ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538)) (term652 B _73536)). Qed.
Lemma lem5824710 {A : Type'} (_73540 : A -> Prop) : (term622 A _73540) = (term622 A _73540).
Proof. exact (eq_refl (term622 A _73540)). Qed.
Lemma lem5824711 {A B : Type'} (_73539 : A) (_73540 : A -> Prop) (_73538 : A -> B) (_73536 : type1400 B) : (term1029 A B _73539 _73536 _73540 _73538) = (term1032 A B _73539 _73540 _73538 _73536).
Proof. exact (MK_COMB (@lem5824710 A _73540) (@lem5824702 A B _73539 _73540 _73538 _73536)). Qed.
Lemma lem5824715 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824716 {A B : Type'} (_73539 : A) (_73538 : A -> B) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1032 A B _73539 _73540 _73538 _73536) = (term1033 A B _73539 _73538 _73540 _73536).
Proof. exact (@lem5824715 ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538)) (term594 A _73540) (term652 B _73536)). Qed.
Lemma lem5824734 {A B : Type'} (_73539 : A) (_73538 : A -> B) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1029 A B _73539 _73536 _73540 _73538) = (term1033 A B _73539 _73538 _73540 _73536).
Proof. exact (TRANS (@lem5824711 A B _73539 _73540 _73538 _73536) (@lem5824716 A B _73539 _73538 _73540 _73536)). Qed.
Lemma lem5824735 {A B : Type'} (_73539 : A) (_73538 : A -> B) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1028 A B _73539 _73536 _73540 _73538) = (term1033 A B _73539 _73538 _73540 _73536).
Proof. exact (TRANS (@lem5824687 A B _73539 _73536 _73540 _73538) (@lem5824734 A B _73539 _73538 _73540 _73536)). Qed.
Lemma lem5824736 {A : Type'} (_73539 : A) (_73540 : A -> Prop) : (term624 A _73539 _73540) = (term624 A _73539 _73540).
Proof. exact (eq_refl (term624 A _73539 _73540)). Qed.
Lemma lem5824737 {A B : Type'} (_73539 : A) (_73538 : A -> B) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1027 A B _73539 _73536 _73540 _73538) = (term1034 A B _73539 _73538 _73540 _73536).
Proof. exact (MK_COMB (@lem5824736 A _73539 _73540) (@lem5824735 A B _73539 _73538 _73540 _73536)). Qed.
Lemma lem5824741 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824742 {A B : Type'} (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1034 A B _73539 _73538 _73540 _73536) = (term1035 A B _73538 _73539 _73540 _73536).
Proof. exact (@lem5824741 ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538)) (term548 A _73539 _73540) (term1036 A B _73540 _73536)). Qed.
Lemma lem5824770 {A B : Type'} (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1027 A B _73539 _73536 _73540 _73538) = (term1035 A B _73538 _73539 _73540 _73536).
Proof. exact (TRANS (@lem5824737 A B _73539 _73538 _73540 _73536) (@lem5824742 A B _73538 _73539 _73540 _73536)). Qed.
Lemma lem5824771 {A B : Type'} (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (_73536 : type1400 B) : (term921 A B _73539 _73536 _73540 _73538) = (term1035 A B _73538 _73539 _73540 _73536).
Proof. exact (TRANS (@lem5824672 A B _73539 _73536 _73540 _73538) (@lem5824770 A B _73538 _73539 _73540 _73536)). Qed.
Lemma lem5824772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5824773 {A B : Type'} (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1037 A B _73539 _73536 _73540 _73538) = (term1038 A B _73538 _73539 _73540 _73536).
Proof. exact (MK_COMB (@lem5824772) (@lem5824771 A B _73538 _73539 _73540 _73536)). Qed.
Lemma lem5824787 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824788 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1028 A B _73539 _73536 _73540 _73538) = (term1029 A B _73539 _73536 _73540 _73538).
Proof. exact (@lem5824787 (term594 A _73540) (term652 B _73536) ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538))). Qed.
Lemma lem5824802 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5824803 {A B : Type'} (_73539 : A) (_73540 : A -> Prop) (_73538 : A -> B) (_73536 : type1400 B) : (term1030 A B _73539 _73536 _73540 _73538) = (term1031 A B _73539 _73540 _73538 _73536).
Proof. exact (@lem5824802 ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538)) (term652 B _73536)). Qed.
Lemma lem5824811 {A : Type'} (_73540 : A -> Prop) : (term622 A _73540) = (term622 A _73540).
Proof. exact (eq_refl (term622 A _73540)). Qed.
Lemma lem5824812 {A B : Type'} (_73539 : A) (_73540 : A -> Prop) (_73538 : A -> B) (_73536 : type1400 B) : (term1029 A B _73539 _73536 _73540 _73538) = (term1032 A B _73539 _73540 _73538 _73536).
Proof. exact (MK_COMB (@lem5824811 A _73540) (@lem5824803 A B _73539 _73540 _73538 _73536)). Qed.
Lemma lem5824816 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824817 {A B : Type'} (_73539 : A) (_73538 : A -> B) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1032 A B _73539 _73540 _73538 _73536) = (term1033 A B _73539 _73538 _73540 _73536).
Proof. exact (@lem5824816 ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538)) (term594 A _73540) (term652 B _73536)). Qed.
Lemma lem5824835 {A B : Type'} (_73539 : A) (_73538 : A -> B) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1029 A B _73539 _73536 _73540 _73538) = (term1033 A B _73539 _73538 _73540 _73536).
Proof. exact (TRANS (@lem5824812 A B _73539 _73540 _73538 _73536) (@lem5824817 A B _73539 _73538 _73540 _73536)). Qed.
Lemma lem5824836 {A B : Type'} (_73539 : A) (_73538 : A -> B) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1028 A B _73539 _73536 _73540 _73538) = (term1033 A B _73539 _73538 _73540 _73536).
Proof. exact (TRANS (@lem5824788 A B _73539 _73536 _73540 _73538) (@lem5824835 A B _73539 _73538 _73540 _73536)). Qed.
Lemma lem5824837 {A : Type'} (_73539 : A) (_73540 : A -> Prop) : (term624 A _73539 _73540) = (term624 A _73539 _73540).
Proof. exact (eq_refl (term624 A _73539 _73540)). Qed.
Lemma lem5824838 {A B : Type'} (_73539 : A) (_73538 : A -> B) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1027 A B _73539 _73536 _73540 _73538) = (term1034 A B _73539 _73538 _73540 _73536).
Proof. exact (MK_COMB (@lem5824837 A _73539 _73540) (@lem5824836 A B _73539 _73538 _73540 _73536)). Qed.
Lemma lem5824842 (q : Prop) (p : Prop) (r : Prop) : (term962 p q r) = (term962 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5824843 {A B : Type'} (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1034 A B _73539 _73538 _73540 _73536) = (term1035 A B _73538 _73539 _73540 _73536).
Proof. exact (@lem5824842 ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538)) (term548 A _73539 _73540) (term1036 A B _73540 _73536)). Qed.
Lemma lem5824871 {A B : Type'} (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (_73536 : type1400 B) : (term1027 A B _73539 _73536 _73540 _73538) = (term1035 A B _73538 _73539 _73540 _73536).
Proof. exact (TRANS (@lem5824838 A B _73539 _73538 _73540 _73536) (@lem5824843 A B _73538 _73539 _73540 _73536)). Qed.
Lemma lem5824872 {A B : Type'} (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (_73536 : type1400 B) : ((term921 A B _73539 _73536 _73540 _73538) = (term1027 A B _73539 _73536 _73540 _73538)) = ((term1035 A B _73538 _73539 _73540 _73536) = (term1035 A B _73538 _73539 _73540 _73536)).
Proof. exact (MK_COMB (@lem5824773 A B _73538 _73539 _73540 _73536) (@lem5824871 A B _73538 _73539 _73540 _73536)). Qed.
Lemma lem5824874 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5824875 (x : Prop) : (x = x) = True.
Proof. exact (@lem5824874 Prop x). Qed.
Lemma lem5824876 {A B : Type'} (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (_73536 : type1400 B) : ((term1035 A B _73538 _73539 _73540 _73536) = (term1035 A B _73538 _73539 _73540 _73536)) = True.
Proof. exact (@lem5824875 (term1035 A B _73538 _73539 _73540 _73536)). Qed.
Lemma lem5824877 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : ((term921 A B _73539 _73536 _73540 _73538) = (term1027 A B _73539 _73536 _73540 _73538)) = True.
Proof. exact (TRANS (@lem5824872 A B _73538 _73539 _73540 _73536) (@lem5824876 A B _73538 _73539 _73540 _73536)). Qed.
Lemma lem5824878 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : True = ((term921 A B _73539 _73536 _73540 _73538) = (term1027 A B _73539 _73536 _73540 _73538)).
Proof. exact (SYM (@lem5824877 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824879 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term921 A B _73539 _73536 _73540 _73538) = (term1027 A B _73539 _73536 _73540 _73538).
Proof. exact (EQ_MP (@lem5824878 A B _73539 _73536 _73540 _73538) (@lem0)). Qed.
Lemma lem5824880 {_120477 A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) (h1 : term99 _120477 A B) : term1027 A B _73539 _73536 _73540 _73538.
Proof. exact (EQ_MP (@lem5824879 A B _73539 _73536 _73540 _73538) (@lem5823289 _120477 A B _73539 _73536 _73540 _73538 h1)). Qed.
Lemma lem5824882 (b : Prop) (a : Prop) : (a \/ b) = (term935 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5824883 {A B : Type'} (_73536 : type1400 B) (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) : (term1027 A B _73539 _73536 _73540 _73538) = (term1039 A B _73536 _73538 _73539 _73540).
Proof. exact (@lem5824882 (term1028 A B _73539 _73536 _73540 _73538) (term548 A _73539 _73540)). Qed.
Lemma lem5824885 (a : Prop) (b : Prop) : (term969 a b) = (term970 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5824886 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1040 A B _73539 _73536 _73540 _73538) = (term1041 A B _73539 _73536 _73540 _73538).
Proof. exact (@lem5824885 (term652 B _73536) (term623 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824888 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824889 {B : Type'} (_73536 : type1400 B) : (term1042 B _73536) = (@I ((B -> B -> B) -> Prop) (@monoidal B) _73536).
Proof. exact (@lem5824888 (@I ((B -> B -> B) -> Prop) (@monoidal B) _73536)). Qed.
Lemma lem5824890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5824891 {B : Type'} (_73536 : type1400 B) : (term1043 B _73536) = (term678 B _73536).
Proof. exact (MK_COMB (@lem5824890) (@lem5824889 B _73536)). Qed.
Lemma lem5824893 (a : Prop) (b : Prop) : (term969 a b) = (term970 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5824894 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1044 A B _73539 _73536 _73540 _73538) = (term1045 A B _73539 _73536 _73540 _73538).
Proof. exact (@lem5824893 (term594 A _73540) ((term610 A B _73536 _73539 _73540 _73538) = (term619 A B _73539 _73536 _73540 _73538))). Qed.
Lemma lem5824896 (a : Prop) : (term937 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5824897 {A : Type'} (_73540 : A -> Prop) : (term938 A _73540) = (@I ((A -> Prop) -> Prop) (@FINITE A) _73540).
Proof. exact (@lem5824896 (@I ((A -> Prop) -> Prop) (@FINITE A) _73540)). Qed.
Lemma lem5824898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5824899 {A : Type'} (_73540 : A -> Prop) : (term1046 A _73540) = (term673 A _73540).
Proof. exact (MK_COMB (@lem5824898) (@lem5824897 A _73540)). Qed.
Lemma lem5824900 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1047 A B _73539 _73536 _73540 _73538) = (term1047 A B _73539 _73536 _73540 _73538).
Proof. exact (eq_refl (term1047 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824901 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1045 A B _73539 _73536 _73540 _73538) = (term1048 A B _73539 _73536 _73540 _73538).
Proof. exact (MK_COMB (@lem5824899 A _73540) (@lem5824900 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824902 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1044 A B _73539 _73536 _73540 _73538) = (term1048 A B _73539 _73536 _73540 _73538).
Proof. exact (TRANS (@lem5824894 A B _73539 _73536 _73540 _73538) (@lem5824901 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824903 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1041 A B _73539 _73536 _73540 _73538) = (term1049 A B _73539 _73536 _73540 _73538).
Proof. exact (MK_COMB (@lem5824891 B _73536) (@lem5824902 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824904 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1040 A B _73539 _73536 _73540 _73538) = (term1049 A B _73539 _73536 _73540 _73538).
Proof. exact (TRANS (@lem5824886 A B _73539 _73536 _73540 _73538) (@lem5824903 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5824906 {A B : Type'} (_73539 : A) (_73536 : type1400 B) (_73540 : A -> Prop) (_73538 : A -> B) : (term1050 A B _73539 _73536 _73540 _73538) = (term1051 A B _73539 _73536 _73540 _73538).
Proof. exact (MK_COMB (@lem5824905) (@lem5824904 A B _73539 _73536 _73540 _73538)). Qed.
Lemma lem5824907 {A : Type'} (_73539 : A) (_73540 : A -> Prop) : (term548 A _73539 _73540) = (term548 A _73539 _73540).
Proof. exact (eq_refl (term548 A _73539 _73540)). Qed.
Lemma lem5824908 {A B : Type'} (_73536 : type1400 B) (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) : (term1039 A B _73536 _73538 _73539 _73540) = (term1052 A B _73536 _73538 _73539 _73540).
Proof. exact (MK_COMB (@lem5824906 A B _73539 _73536 _73540 _73538) (@lem5824907 A _73539 _73540)). Qed.
Lemma lem5824909 {A B : Type'} (_73536 : type1400 B) (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) : (term1027 A B _73539 _73536 _73540 _73538) = (term1052 A B _73536 _73538 _73539 _73540).
Proof. exact (TRANS (@lem5824883 A B _73536 _73538 _73539 _73540) (@lem5824908 A B _73536 _73538 _73539 _73540)). Qed.
Lemma lem5824911 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term7 A) (h3 : term258 A B a op s f) : term1053 A B op s a f.
Proof. exact (conj (@lem5824293 A B a op s f h2 h3) (@lem5824665 A B a op s f h1 h3)). Qed.
Lemma lem5824912 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term7 A) (h3 : term258 A B a op s f) : term1054 A B op s a f.
Proof. exact (conj (@lem5824260 A B a op s f h3) (@lem5824911 A B a op s f h1 h2 h3)). Qed.
Lemma lem5824914 {_120477 A B : Type'} (_73536 : type1400 B) (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (h1 : term99 _120477 A B) : term1052 A B _73536 _73538 _73539 _73540.
Proof. exact (EQ_MP (@lem5824909 A B _73536 _73538 _73539 _73540) (@lem5824880 _120477 A B _73539 _73536 _73540 _73538 h1)). Qed.
Lemma lem5824915 {_120477 A B : Type'} (_73536 : type1400 B) (_73538 : A -> B) (_73539 : A) (_73540 : A -> Prop) (h1 : term99 _120477 A B) : term1052 A B _73536 _73538 _73539 _73540.
Proof. exact (@lem5824914 _120477 A B _73536 _73538 _73539 _73540 h1). Qed.
Lemma lem5824916 {_120477 A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (a : A) (h1 : term99 _120477 A B) : term1055 A B op f s a.
Proof. exact (@lem5824915 _120477 A B op f a (term542 A s a) h1). Qed.
Lemma lem5824919 {_120477 A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term7 A) (h3 : term99 _120477 A B) (h4 : term258 A B a op s f) : term1056 A s a.
Proof. exact (@lem5824916 _120477 A B op f s a h3 (@lem5824912 A B a op s f h1 h2 h4)). Qed.
Lemma lem5824920 {_120477 A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term7 A) (h3 : term99 _120477 A B) (h4 : term258 A B a op s f) : term1057 A s a.
Proof. exact (fun h0 : term1058 A s a => @lem5824919 _120477 A B a op s f h1 h2 h3 h4). Qed.
Lemma lem5824922 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824923 {A : Type'} (s : A -> Prop) (a : A) : (term1057 A s a) = (term1056 A s a).
Proof. exact (@lem5824922 (term1056 A s a)). Qed.
Lemma lem5824924 {_120477 A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term7 A) (h3 : term99 _120477 A B) (h4 : term258 A B a op s f) : term1056 A s a.
Proof. exact (EQ_MP (@lem5824923 A s a) (@lem5824920 _120477 A B a op s f h1 h2 h3 h4)). Qed.
Lemma lem5824926 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5824927 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5824926 A x). Qed.
Lemma lem5824928 {A : Type'} (a : A) : a = a.
Proof. exact (@lem5824927 A a). Qed.
Lemma lem5824929 {A : Type'} (a : A) : term1059 A a.
Proof. exact (fun h0 : term1060 A a => @lem5824928 A a). Qed.
Lemma lem5824931 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824932 {A : Type'} (a : A) : (term1059 A a) = (a = a).
Proof. exact (@lem5824931 (a = a)). Qed.
Lemma lem5824933 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem5824932 A a) (@lem5824929 A a)). Qed.
Lemma lem5824935 (a : Prop) (b : Prop) : (term1061 a b) = (term1062 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5824936 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) : (term920 A _73563 _73564 _73565) = (term1063 A _73563 _73564 _73565).
Proof. exact (@lem5824935 (term562 A _73564 _73563 _73565) (_73564 = _73565)). Qed.
Lemma lem5824938 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5824939 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) : (term1063 A _73563 _73564 _73565) = (term1064 A _73563 _73564 _73565).
Proof. exact (@lem5824938 (term1065 A _73563 _73564 _73565)). Qed.
Lemma lem5824940 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) : (term920 A _73563 _73564 _73565) = (term1064 A _73563 _73564 _73565).
Proof. exact (TRANS (@lem5824936 A _73563 _73564 _73565) (@lem5824939 A _73563 _73564 _73565)). Qed.
Lemma lem5824942 {_120477 A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term7 A) (h3 : term99 _120477 A B) (h4 : term258 A B a op s f) : term1066 A s a.
Proof. exact (conj (@lem5824924 _120477 A B a op s f h1 h2 h3 h4) (@lem5824933 A a)). Qed.
Lemma lem5824944 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) (h1 : term8 A) : term1064 A _73563 _73564 _73565.
Proof. exact (EQ_MP (@lem5824940 A _73563 _73564 _73565) (@lem5823209 A _73563 _73564 _73565 h1)). Qed.
Lemma lem5824945 {A : Type'} (_73563 : A -> Prop) (_73564 : A) (_73565 : A) (h1 : term8 A) : term1064 A _73563 _73564 _73565.
Proof. exact (@lem5824944 A _73563 _73564 _73565 h1). Qed.
Lemma lem5824946 {A : Type'} (s : A -> Prop) (a : A) (h1 : term8 A) : term1067 A s a.
Proof. exact (@lem5824945 A s a a h1). Qed.
Lemma lem5824949 {_120477 A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term258 A B a op s f) : False.
Proof. exact (@lem5824946 A s a h2 (@lem5824942 _120477 A B a op s f h1 h3 h4 h5)). Qed.
Lemma lem5824950 {_120477 A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term258 A B a op s f) : term1068.
Proof. exact (fun h0 : ~ False => @lem5824949 _120477 A B a op s f h1 h2 h3 h4 h5). Qed.
Lemma lem5824952 (p : Prop) : (term933 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5824953 : term1068 = False.
Proof. exact (@lem5824952 False). Qed.
Lemma lem5824954 {_120477 A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term258 A B a op s f) : False.
Proof. exact (EQ_MP (@lem5824953) (@lem5824950 _120477 A B a op s f h1 h2 h3 h4 h5)). Qed.
Lemma lem5824955 {_120477 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term261 A B op s f) : False.
Proof. exact (ex_elim (@lem5818531 A B op s f h5) (fun a : A => fun h0 : term260 A B op s f a => @lem5824954 _120477 A B a op s f h1 h2 h3 h4 h0)). Qed.
Lemma lem5824956 {_120477 A B : Type'} (op : type1400 B) (f : A -> B) (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term263 A B op f) : False.
Proof. exact (ex_elim (@lem5818530 A B op f h5) (fun s : A -> Prop => fun h0 : term262 A B op f s => @lem5824955 _120477 A B op s f h1 h2 h3 h4 h0)). Qed.
Lemma lem5824957 {_120477 A B : Type'} (op : type1400 B) (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term265 A B op) : False.
Proof. exact (ex_elim (@lem5818529 A B op h5) (fun f : A -> B => fun h0 : term264 A B op f => @lem5824956 _120477 A B op f h1 h2 h3 h4 h0)). Qed.
Lemma lem5824958 {_120477 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term3 A B) : False.
Proof. exact (ex_elim (@lem5813622 A B h5) (fun op : type1400 B => fun h0 : term266 A B op => @lem5824957 _120477 A B op h1 h2 h3 h4 h0)). Qed.
Lemma lem5824959 {_120477 _120521 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term3 A B) : term1069 _120521 A B.
Proof. exact (fun h0 : term91 _120521 A B => @lem5824958 _120477 A B h1 h2 h3 h4 h5). Qed.
Lemma lem5824960 {_120521 A B : Type'} : (term1069 _120521 A B) = (term92 _120521 A B).
Proof. exact (@lem69 (term91 _120521 A B)). Qed.
Lemma lem5824961 {_120477 _120521 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term99 _120477 A B) (h5 : term3 A B) : term92 _120521 A B.
Proof. exact (EQ_MP (@lem5824960 _120521 A B) (@lem5824959 _120477 _120521 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem5824962 {_120477 _120521 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term3 A B) : term101 _120477 _120521 A B.
Proof. exact (fun h0 : term99 _120477 A B => @lem5824961 _120477 _120521 A B h1 h2 h3 h0 h4). Qed.
Lemma lem5824963 {_120477 _120521 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term3 A B) : term102 _120477 _120521 A B.
Proof. exact (fun h0 : term99 _120477 _120521 B => @lem5824962 _120477 _120521 A B h1 h2 h3 h4). Qed.
Lemma lem5824964 {_120477 _120519 _120521 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term7 A) (h4 : term3 A B) : term141 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term139 _120477 _120519 A => @lem5824963 _120477 _120521 A B h1 h2 h3 h4). Qed.
Lemma lem5824965 {_120477 _120519 _120521 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term3 A B) : term146 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term7 A => @lem5824964 _120477 _120519 _120521 A B h1 h2 h0 h3). Qed.
Lemma lem5824966 {_120477 _120519 _120521 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term3 A B) : term147 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term7 _120521 => @lem5824965 _120477 _120519 _120521 A B h1 h2 h3). Qed.
Lemma lem5824967 {_120477 _120519 _120521 A B : Type'} (h1 : term9 A) (h2 : term8 A) (h3 : term3 A B) : term155 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term8 B => @lem5824966 _120477 _120519 _120521 A B h1 h2 h3). Qed.
Lemma lem5824968 {_120477 _120519 _120521 A B : Type'} (h1 : term9 A) (h2 : term3 A B) : term156 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term8 A => @lem5824967 _120477 _120519 _120521 A B h1 h0 h2). Qed.
Lemma lem5824969 {_120477 _120519 _120521 A B : Type'} (h1 : term9 A) (h2 : term3 A B) : term157 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term8 _120521 => @lem5824968 _120477 _120519 _120521 A B h1 h2). Qed.
Lemma lem5824970 {_120477 _120519 _120521 A B : Type'} (h1 : term9 A) (h2 : term3 A B) : term158 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term8 _120519 => @lem5824969 _120477 _120519 _120521 A B h1 h2). Qed.
Lemma lem5824971 {_120477 _120519 _120521 A B : Type'} (h1 : term9 A) (h2 : term3 A B) : term163 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term9 B => @lem5824970 _120477 _120519 _120521 A B h1 h2). Qed.
Lemma lem5824972 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term164 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term9 A => @lem5824971 _120477 _120519 _120521 A B h0 h1). Qed.
Lemma lem5824973 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term165 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term9 _120521 => @lem5824972 _120477 _120519 _120521 A B h1). Qed.
Lemma lem5824974 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term166 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term9 _120519 => @lem5824973 _120477 _120519 _120521 A B h1). Qed.
Lemma lem5824975 {_120477 _120519 _120521 A B : Type'} : term176 _120477 _120519 _120521 A B.
Proof. exact (fun h0 : term3 A B => @lem5824974 _120477 _120519 _120521 A B h0). Qed.
Lemma lem5824976 {_120477 _120519 _120521 A B : Type'} : term10 _120477 _120519 _120521 A B.
Proof. exact (EQ_MP (@lem5813391 _120477 _120519 _120521 A B) (@lem5824975 _120477 _120519 _120521 A B)). Qed.
Lemma lem5824978 {_120477 _120519 _120521 A B : Type'} : term10 _120477 _120519 _120521 A B.
Proof. exact (@lem5811991 _120477 _120519 _120521 A B (@lem5824976 _120477 _120519 _120521 A B)). Qed.
Lemma lem5824979 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term45 _120477 _120519 _120521 A B.
Proof. exact (@lem5824978 _120477 _120519 _120521 A B (@lem5811950 A B h1)). Qed.
Lemma lem5824980 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term43 _120477 _120519 _120521 A B.
Proof. exact (@lem5824979 _120477 _120519 _120521 A B h1 (@lem5811969 _120519)). Qed.
Lemma lem5824981 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term41 _120477 _120519 _120521 A B.
Proof. exact (@lem5824980 _120477 _120519 _120521 A B h1 (@lem5811967 _120521)). Qed.
Lemma lem5824982 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term39 _120477 _120519 _120521 A B.
Proof. exact (@lem5824981 _120477 _120519 _120521 A B h1 (@lem5811966 A)). Qed.
Lemma lem5824983 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term36 _120477 _120519 _120521 A B.
Proof. exact (@lem5824982 _120477 _120519 _120521 A B h1 (@lem5811968 B)). Qed.
Lemma lem5824984 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term34 _120477 _120519 _120521 A B.
Proof. exact (@lem5824983 _120477 _120519 _120521 A B h1 (@lem5811965 _120519)). Qed.
Lemma lem5824985 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term32 _120477 _120519 _120521 A B.
Proof. exact (@lem5824984 _120477 _120519 _120521 A B h1 (@lem5811961 _120521)). Qed.
Lemma lem5824986 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term30 _120477 _120519 _120521 A B.
Proof. exact (@lem5824985 _120477 _120519 _120521 A B h1 (@lem5811960 A)). Qed.
Lemma lem5824987 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term27 _120477 _120519 _120521 A B.
Proof. exact (@lem5824986 _120477 _120519 _120521 A B h1 (@lem5811964 B)). Qed.
Lemma lem5824988 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term25 _120477 _120519 _120521 A B.
Proof. exact (@lem5824987 _120477 _120519 _120521 A B h1 (@lem5811958 _120521)). Qed.
Lemma lem5824989 {_120477 _120519 _120521 A B : Type'} (h1 : term3 A B) : term22 _120477 _120519 _120521 A B.
Proof. exact (@lem5824988 _120477 _120519 _120521 A B h1 (@lem5811957 A)). Qed.
Lemma lem5824990 {_120477 _120521 A B : Type'} (h1 : term3 A B) : term19 _120477 _120521 A B.
Proof. exact (@lem5824989 _120477 Prop _120521 A B h1 (@lem5811954 _120477 Prop A)). Qed.
Lemma lem5824991 {_120477 _120521 A B : Type'} (h1 : term3 A B) : term17 _120477 _120521 A B.
Proof. exact (@lem5824990 _120477 _120521 A B h1 (@lem5811951 _120477 _120521 B)). Qed.
Lemma lem5824992 {_120521 A B : Type'} (h1 : term3 A B) : term14 _120521 A B.
Proof. exact (@lem5824991 Prop _120521 A B h1 (@lem5811955 Prop A B)). Qed.
Lemma lem5824993 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (@lem5824992 Prop A B h1 (@lem5811953 Prop A B)). Qed.
Lemma lem5824994 {A B : Type'} (h1 : term3 A B) : (term3 A B) = False.
Proof. exact (prop_ext (fun h2 : term3 A B => @lem5824993 A B h1) (fun h2 : False => @lem5811950 A B h1)). Qed.
Lemma lem5824995 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (EQ_MP (@lem5824994 A B h1) (@lem5811950 A B h1)). Qed.
Lemma lem5824996 {A B : Type'} : term2 A B.
Proof. exact (fun h0 : term3 A B => @lem5824995 A B h0). Qed.
Lemma lem5824997 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem5811949 A B) (@lem5824996 A B)). Qed.
