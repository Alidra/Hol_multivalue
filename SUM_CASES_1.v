Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CASES_1_term_abbrevs.
Require Import DELETE_spec.
Require Import SUM_CASES_spec.
Require Import SUM_DELETE_spec.
Require Import SUM_SING_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7188905 {_133036 : Type'} (f : _133036 -> real) : term0 _133036 f.
Proof. exact (@lem7123532 _133036 f). Qed.
Lemma lem7188906 {_133036 : Type'} (f : _133036 -> real) : (term0 _133036 f) = (term1 _133036 f).
Proof. exact (eq_refl (term0 _133036 f)). Qed.
Lemma lem7188907 {_133036 : Type'} (f : _133036 -> real) : term1 _133036 f.
Proof. exact (EQ_MP (@lem7188906 _133036 f) (@lem7188905 _133036 f)). Qed.
Lemma lem7188908 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : term2 _133036 f x.
Proof. exact (@lem7188907 _133036 f x). Qed.
Lemma lem7188909 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term2 _133036 f x) = ((term3 _133036 x f) = (f x)).
Proof. exact (eq_refl (term2 _133036 f x)). Qed.
Lemma lem7188926 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7188927 {_135477 : Type'} (s : _135477 -> Prop) (t : _135477 -> Prop) : (s = t) = (term4 _135477 s t).
Proof. exact (@lem7188926 _135477 s t). Qed.
Lemma lem7188928 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : ((term5 _135477 s a) = (@INSERT _135477 a (@EMPTY _135477))) = (term6 _135477 s a).
Proof. exact (@lem7188927 _135477 (term5 _135477 s a) (@INSERT _135477 a (@EMPTY _135477))). Qed.
Lemma lem7188947 {_135477 : Type'} (a : _135477) (s : _135477 -> Prop) : (term7 _135477 a s) = (term7 _135477 a s).
Proof. exact (eq_refl (term7 _135477 a s)). Qed.
Lemma lem7188948 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term8 _135477 s a) = (term9 _135477 s a).
Proof. exact (MK_COMB (@lem7188947 _135477 a s) (@lem7188928 _135477 s a)). Qed.
Lemma lem7188951 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term9 _135477 s a) = (term8 _135477 s a).
Proof. exact (SYM (@lem7188948 _135477 s a)). Qed.
Lemma lem7188955 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7188956 {_135477 : Type'} (P : _135477 -> Prop) (x : _135477) : (@IN _135477 x P) = (P x).
Proof. exact (@lem7188955 _135477 P x). Qed.
Lemma lem7188957 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (@IN _135477 a s) = (s a).
Proof. exact (@lem7188956 _135477 s a). Qed.
Lemma lem7188958 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7188959 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term7 _135477 a s) = (term10 _135477 s a).
Proof. exact (MK_COMB (@lem7188958) (@lem7188957 _135477 s a)). Qed.
Lemma lem7188967 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem7188968 {_135477 : Type'} (p : _135477 -> Prop) (x : _135477) : (term11 _135477 x p) = (p x).
Proof. exact (@lem7188967 _135477 p x). Qed.
Lemma lem7188969 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (x : _135477) : (term12 _135477 x s a) = (term13 _135477 s a x).
Proof. exact (@lem7188968 _135477 (term14 _135477 s a) x). Qed.
Lemma lem7188970 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term13 _135477 s a x) = (term15 _135477 s x a).
Proof. exact (eq_refl (term13 _135477 s a x)). Qed.
Lemma lem7188971 {_135477 : Type'} (GEN_PVAR_330 : _135477) : (@SETSPEC _135477 GEN_PVAR_330) = (@SETSPEC _135477 GEN_PVAR_330).
Proof. exact (eq_refl (@SETSPEC _135477 GEN_PVAR_330)). Qed.
Lemma lem7188972 {_135477 : Type'} (GEN_PVAR_330 : _135477) (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term16 _135477 GEN_PVAR_330 s a x) = (term17 _135477 GEN_PVAR_330 s x a).
Proof. exact (MK_COMB (@lem7188971 _135477 GEN_PVAR_330) (@lem7188970 _135477 s x a)). Qed.
Lemma lem7188973 {_135477 : Type'} (x : _135477) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7188974 {_135477 : Type'} (GEN_PVAR_330 : _135477) (s : _135477 -> Prop) (a : _135477) (x : _135477) : (term18 _135477 GEN_PVAR_330 s a x) = (term19 _135477 GEN_PVAR_330 s a x).
Proof. exact (MK_COMB (@lem7188972 _135477 GEN_PVAR_330 s x a) (@lem7188973 _135477 x)). Qed.
Lemma lem7188975 {_135477 : Type'} (GEN_PVAR_330 : _135477) (s : _135477 -> Prop) (a : _135477) : (term20 _135477 GEN_PVAR_330 s a) = (term21 _135477 GEN_PVAR_330 s a).
Proof. exact (fun_ext (fun x : _135477 => @lem7188974 _135477 GEN_PVAR_330 s a x)). Qed.
Lemma lem7188976 {_135477 : Type'} : (@ex _135477) = (@ex _135477).
Proof. exact (eq_refl (@ex _135477)). Qed.
Lemma lem7188977 {_135477 : Type'} (GEN_PVAR_330 : _135477) (s : _135477 -> Prop) (a : _135477) : (term22 _135477 GEN_PVAR_330 s a) = (term23 _135477 GEN_PVAR_330 s a).
Proof. exact (MK_COMB (@lem7188976 _135477) (@lem7188975 _135477 GEN_PVAR_330 s a)). Qed.
Lemma lem7188978 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term24 _135477 s a) = (term25 _135477 s a).
Proof. exact (fun_ext (fun GEN_PVAR_330 : _135477 => @lem7188977 _135477 GEN_PVAR_330 s a)). Qed.
Lemma lem7188979 {_135477 : Type'} : (@GSPEC _135477) = (@GSPEC _135477).
Proof. exact (eq_refl (@GSPEC _135477)). Qed.
Lemma lem7188980 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term26 _135477 s a) = (term5 _135477 s a).
Proof. exact (MK_COMB (@lem7188979 _135477) (@lem7188978 _135477 s a)). Qed.
Lemma lem7188981 {_135477 : Type'} (x : _135477) : (@IN _135477 x) = (@IN _135477 x).
Proof. exact (eq_refl (@IN _135477 x)). Qed.
Lemma lem7188982 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) : (term12 _135477 x s a) = (term27 _135477 x s a).
Proof. exact (MK_COMB (@lem7188981 _135477 x) (@lem7188980 _135477 s a)). Qed.
Lemma lem7188983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7188984 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) : (term28 _135477 x s a) = (term29 _135477 x s a).
Proof. exact (MK_COMB (@lem7188983) (@lem7188982 _135477 x s a)). Qed.
Lemma lem7188985 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term13 _135477 s a x) = (term15 _135477 s x a).
Proof. exact (eq_refl (term13 _135477 s a x)). Qed.
Lemma lem7188986 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : ((term12 _135477 x s a) = (term13 _135477 s a x)) = ((term27 _135477 x s a) = (term15 _135477 s x a)).
Proof. exact (MK_COMB (@lem7188984 _135477 x s a) (@lem7188985 _135477 s x a)). Qed.
Lemma lem7188987 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term27 _135477 x s a) = (term15 _135477 s x a).
Proof. exact (EQ_MP (@lem7188986 _135477 s x a) (@lem7188969 _135477 s a x)). Qed.
Lemma lem7188991 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7188992 {_135477 : Type'} (P : _135477 -> Prop) (x : _135477) : (@IN _135477 x P) = (P x).
Proof. exact (@lem7188991 _135477 P x). Qed.
Lemma lem7188993 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) : (@IN _135477 x s) = (s x).
Proof. exact (@lem7188992 _135477 s x). Qed.
Lemma lem7188994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7188995 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) : (term30 _135477 x s) = (term31 _135477 s x).
Proof. exact (MK_COMB (@lem7188994) (@lem7188993 _135477 s x)). Qed.
Lemma lem7188998 {_135477 : Type'} (x : _135477) (a : _135477) : (x = a) = (x = a).
Proof. exact (eq_refl (x = a)). Qed.
Lemma lem7188999 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term15 _135477 s x a) = (term32 _135477 s x a).
Proof. exact (MK_COMB (@lem7188995 _135477 s x) (@lem7188998 _135477 x a)). Qed.
Lemma lem7189002 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term27 _135477 x s a) = (term32 _135477 s x a).
Proof. exact (TRANS (@lem7188987 _135477 s x a) (@lem7188999 _135477 s x a)). Qed.
Lemma lem7189003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7189004 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term29 _135477 x s a) = (term33 _135477 s x a).
Proof. exact (MK_COMB (@lem7189003) (@lem7189002 _135477 s x a)). Qed.
Lemma lem7189006 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term34 A x y s) = (term35 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem7189007 {_135477 : Type'} (y : _135477) (x : _135477) (s : _135477 -> Prop) : (term34 _135477 x y s) = (term35 _135477 y x s).
Proof. exact (@lem7189006 _135477 y x s). Qed.
Lemma lem7189008 {_135477 : Type'} (a : _135477) (x : _135477) : (term36 _135477 x a) = (term37 _135477 a x).
Proof. exact (@lem7189007 _135477 a x (@EMPTY _135477)). Qed.
Lemma lem7189014 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem7189015 {_135477 : Type'} (x : _135477) : (@IN _135477 x (@EMPTY _135477)) = False.
Proof. exact (@lem7189014 _135477 x). Qed.
Lemma lem7189016 {_135477 : Type'} (x : _135477) (a : _135477) : (term38 _135477 x a) = (term38 _135477 x a).
Proof. exact (eq_refl (term38 _135477 x a)). Qed.
Lemma lem7189017 {_135477 : Type'} (x : _135477) (a : _135477) : (term37 _135477 a x) = (term39 _135477 x a).
Proof. exact (MK_COMB (@lem7189016 _135477 x a) (@lem7189015 _135477 x)). Qed.
Lemma lem7189019 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem7189020 {_135477 : Type'} (x : _135477) (a : _135477) : (term39 _135477 x a) = (x = a).
Proof. exact (@lem7189019 (x = a)). Qed.
Lemma lem7189023 {_135477 : Type'} (x : _135477) (a : _135477) : (term37 _135477 a x) = (x = a).
Proof. exact (TRANS (@lem7189017 _135477 x a) (@lem7189020 _135477 x a)). Qed.
Lemma lem7189024 {_135477 : Type'} (x : _135477) (a : _135477) : (term36 _135477 x a) = (x = a).
Proof. exact (TRANS (@lem7189008 _135477 a x) (@lem7189023 _135477 x a)). Qed.
Lemma lem7189025 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : ((term27 _135477 x s a) = (term36 _135477 x a)) = ((term32 _135477 s x a) = (x = a)).
Proof. exact (MK_COMB (@lem7189004 _135477 s x a) (@lem7189024 _135477 x a)). Qed.
Lemma lem7189028 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term40 _135477 s a) = (term41 _135477 s a).
Proof. exact (fun_ext (fun x : _135477 => @lem7189025 _135477 s x a)). Qed.
Lemma lem7189029 {_135477 : Type'} : (@all _135477) = (@all _135477).
Proof. exact (eq_refl (@all _135477)). Qed.
Lemma lem7189030 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term6 _135477 s a) = (term42 _135477 s a).
Proof. exact (MK_COMB (@lem7189029 _135477) (@lem7189028 _135477 s a)). Qed.
Lemma lem7189035 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term9 _135477 s a) = (term43 _135477 s a).
Proof. exact (MK_COMB (@lem7188959 _135477 s a) (@lem7189030 _135477 s a)). Qed.
Lemma lem7189038 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term43 _135477 s a) = (term9 _135477 s a).
Proof. exact (SYM (@lem7189035 _135477 s a)). Qed.
Lemma lem7189040 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7189041 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term43 _135477 s a) = (term45 _135477 s a).
Proof. exact (@lem7189040 (term43 _135477 s a)). Qed.
Lemma lem7189042 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term45 _135477 s a) = (term43 _135477 s a).
Proof. exact (SYM (@lem7189041 _135477 s a)). Qed.
Lemma lem7189043 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term46 _135477 s a) : term46 _135477 s a.
Proof. exact (h1). Qed.
Lemma lem7189046 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term45 _135477 s a) : term45 _135477 s a.
Proof. exact (h1). Qed.
Lemma lem7189047 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term47 _135477 s a.
Proof. exact (fun h0 : term45 _135477 s a => @lem7189046 _135477 s a h0). Qed.
Lemma lem7189048 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term47 _135477 s a) : term47 _135477 s a.
Proof. exact (h1). Qed.
Lemma lem7189049 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term45 _135477 s a) : term45 _135477 s a.
Proof. exact (h1). Qed.
Lemma lem7189050 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term45 _135477 s a) (h2 : term47 _135477 s a) : term45 _135477 s a.
Proof. exact (@lem7189048 _135477 s a h2 (@lem7189049 _135477 s a h1)). Qed.
Lemma lem7189051 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term45 _135477 s a) : term48 _135477 s a.
Proof. exact (fun h0 : term47 _135477 s a => @lem7189050 _135477 s a h1 h0). Qed.
Lemma lem7189052 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term47 _135477 s a) : term47 _135477 s a.
Proof. exact (h1). Qed.
Lemma lem7189053 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term45 _135477 s a) (h2 : term47 _135477 s a) : term45 _135477 s a.
Proof. exact (@lem7189051 _135477 s a h1 (@lem7189052 _135477 s a h2)). Qed.
Lemma lem7189054 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term47 _135477 s a) : term47 _135477 s a.
Proof. exact (fun h0 : term45 _135477 s a => @lem7189053 _135477 s a h0 h1). Qed.
Lemma lem7189055 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term49 _135477 s a.
Proof. exact (fun h0 : term47 _135477 s a => @lem7189054 _135477 s a h0). Qed.
Lemma lem7189058 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term47 _135477 s a.
Proof. exact (@lem7189055 _135477 s a (@lem7189047 _135477 s a)). Qed.
Lemma lem7189059 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term47 _135477 s a.
Proof. exact (@lem7189058 _135477 s a). Qed.
Lemma lem7189069 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7189070 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term45 _135477 s a) = (term50 _135477 s a).
Proof. exact (@lem7189069 (term46 _135477 s a)). Qed.
Lemma lem7189072 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7189073 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term50 _135477 s a) = (term43 _135477 s a).
Proof. exact (@lem7189072 (term43 _135477 s a)). Qed.
Lemma lem7189076 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term45 _135477 s a) = (term43 _135477 s a).
Proof. exact (TRANS (@lem7189070 _135477 s a) (@lem7189073 _135477 s a)). Qed.
Lemma lem7189083 {_135477 : Type'} (a : _135477) : (term52 _135477 a) = (term53 _135477 a).
Proof. exact (fun_ext (fun s : _135477 -> Prop => @lem7189076 _135477 s a)). Qed.
Lemma lem7189084 {_135477 : Type'} : (@all (_135477 -> Prop)) = (@all (_135477 -> Prop)).
Proof. exact (eq_refl (@all (_135477 -> Prop))). Qed.
Lemma lem7189085 {_135477 : Type'} (a : _135477) : (term54 _135477 a) = (term55 _135477 a).
Proof. exact (MK_COMB (@lem7189084 _135477) (@lem7189083 _135477 a)). Qed.
Lemma lem7189090 {_135477 : Type'} : (term56 _135477) = (term57 _135477).
Proof. exact (fun_ext (fun a : _135477 => @lem7189085 _135477 a)). Qed.
Lemma lem7189091 {_135477 : Type'} : (@all _135477) = (@all _135477).
Proof. exact (eq_refl (@all _135477)). Qed.
Lemma lem7189100 {_135477 : Type'} : (term58 _135477) = (term59 _135477).
Proof. exact (MK_COMB (@lem7189091 _135477) (@lem7189090 _135477)). Qed.
Lemma lem7189109 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : ((term32 _135477 s x a) = (x = a)) = ((term32 _135477 s x a) = (x = a)).
Proof. exact (eq_refl ((term32 _135477 s x a) = (x = a))). Qed.
Lemma lem7189110 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term41 _135477 s a) = (term41 _135477 s a).
Proof. exact (fun_ext (fun x : _135477 => @lem7189109 _135477 s x a)). Qed.
Lemma lem7189111 {_135477 : Type'} : (@all _135477) = (@all _135477).
Proof. exact (eq_refl (@all _135477)). Qed.
Lemma lem7189112 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term42 _135477 s a) = (term42 _135477 s a).
Proof. exact (MK_COMB (@lem7189111 _135477) (@lem7189110 _135477 s a)). Qed.
Lemma lem7189115 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term10 _135477 s a) = (term10 _135477 s a).
Proof. exact (eq_refl (term10 _135477 s a)). Qed.
Lemma lem7189116 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term43 _135477 s a) = (term43 _135477 s a).
Proof. exact (MK_COMB (@lem7189115 _135477 s a) (@lem7189112 _135477 s a)). Qed.
Lemma lem7189117 {_135477 : Type'} (a : _135477) : (term53 _135477 a) = (term53 _135477 a).
Proof. exact (fun_ext (fun s : _135477 -> Prop => @lem7189116 _135477 s a)). Qed.
Lemma lem7189118 {_135477 : Type'} : (@all (_135477 -> Prop)) = (@all (_135477 -> Prop)).
Proof. exact (eq_refl (@all (_135477 -> Prop))). Qed.
Lemma lem7189119 {_135477 : Type'} (a : _135477) : (term55 _135477 a) = (term55 _135477 a).
Proof. exact (MK_COMB (@lem7189118 _135477) (@lem7189117 _135477 a)). Qed.
Lemma lem7189120 {_135477 : Type'} : (term57 _135477) = (term57 _135477).
Proof. exact (fun_ext (fun a : _135477 => @lem7189119 _135477 a)). Qed.
Lemma lem7189121 {_135477 : Type'} : (@all _135477) = (@all _135477).
Proof. exact (eq_refl (@all _135477)). Qed.
Lemma lem7189122 {_135477 : Type'} : (term59 _135477) = (term59 _135477).
Proof. exact (MK_COMB (@lem7189121 _135477) (@lem7189120 _135477)). Qed.
Lemma lem7189147 {_135477 : Type'} : (term58 _135477) = (term59 _135477).
Proof. exact (TRANS (@lem7189100 _135477) (@lem7189122 _135477)). Qed.
Lemma lem7189148 {_135477 : Type'} : (term59 _135477) = (term58 _135477).
Proof. exact (SYM (@lem7189147 _135477)). Qed.
Lemma lem7189151 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7189152 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : ((term32 _135477 s x a) = (x = a)) = (term60 _135477 s x a).
Proof. exact (@lem7189151 ((term32 _135477 s x a) = (x = a))). Qed.
Lemma lem7189153 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term60 _135477 s x a) = ((term32 _135477 s x a) = (x = a)).
Proof. exact (SYM (@lem7189152 _135477 s x a)). Qed.
Lemma lem7189154 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term61 _135477 s x a) : term61 _135477 s x a.
Proof. exact (h1). Qed.
Lemma lem7189160 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7189169 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term62 _135477 s x a) = (term63 _135477 s x a).
Proof. exact (@lem17045 (s x) (x = a)). Qed.
Lemma lem7189174 {_135477 : Type'} (x : _135477) (a : _135477) : (x = a) = (x = a).
Proof. exact (eq_refl (x = a)). Qed.
Lemma lem7189175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7189176 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term64 _135477 s x a) = (term65 _135477 s x a).
Proof. exact (MK_COMB (@lem7189175) (@lem7189169 _135477 s x a)). Qed.
Lemma lem7189177 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term66 _135477 s x a) = (term67 _135477 s x a).
Proof. exact (MK_COMB (@lem7189176 _135477 s x a) (@lem7189174 _135477 x a)). Qed.
Lemma lem7189182 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term68 _135477 s x a) = (term68 _135477 s x a).
Proof. exact (eq_refl (term68 _135477 s x a)). Qed.
Lemma lem7189183 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term69 _135477 s x a) = (term70 _135477 s x a).
Proof. exact (MK_COMB (@lem7189182 _135477 s x a) (@lem7189177 _135477 s x a)). Qed.
Lemma lem7189184 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term61 _135477 s x a) = (term69 _135477 s x a).
Proof. exact (@lem17646 (term32 _135477 s x a) (x = a)). Qed.
Lemma lem7189189 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) : (term61 _135477 s x a) = (term70 _135477 s x a).
Proof. exact (TRANS (@lem7189184 _135477 s x a) (@lem7189183 _135477 s x a)). Qed.
Lemma lem7189194 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7189242 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term61 _135477 s x a) : term70 _135477 s x a.
Proof. exact (EQ_MP (@lem7189189 _135477 s x a) (@lem7189154 _135477 s x a h1)). Qed.
Lemma lem7189243 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : term71 _135477 s x a.
Proof. exact (h1). Qed.
Lemma lem7189244 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term67 _135477 s x a) : term67 _135477 s x a.
Proof. exact (h1). Qed.
Lemma lem7189246 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : term32 _135477 s x a.
Proof. exact (proj1 (@lem7189243 _135477 s x a h1)). Qed.
Lemma lem7189250 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term67 _135477 s x a) : term63 _135477 s x a.
Proof. exact (proj1 (@lem7189244 _135477 s x a h1)). Qed.
Lemma lem7189272 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7189280 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (h1 : term72 _135477 s x) : term72 _135477 s x.
Proof. exact (h1). Qed.
Lemma lem7189292 {_135477 : Type'} (x : _135477) (a : _135477) (h1 : term73 _135477 x a) : term73 _135477 x a.
Proof. exact (h1). Qed.
Lemma lem7189296 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : term73 _135477 x a.
Proof. exact (proj2 (@lem7189243 _135477 s x a h1)). Qed.
Lemma lem7189300 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : x = a.
Proof. exact (proj2 (@lem7189246 _135477 s x a h1)). Qed.
Lemma lem7189302 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7189304 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term67 _135477 s x a) : x = a.
Proof. exact (proj2 (@lem7189244 _135477 s x a h1)). Qed.
Lemma lem7189306 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (h1 : term72 _135477 s x) : term72 _135477 s x.
Proof. exact (h1). Qed.
Lemma lem7189310 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term67 _135477 s x a) : x = a.
Proof. exact (proj2 (@lem7189244 _135477 s x a h1)). Qed.
Lemma lem7189312 {_135477 : Type'} (x : _135477) (a : _135477) (h1 : term73 _135477 x a) : term73 _135477 x a.
Proof. exact (h1). Qed.
Lemma lem7189341 {_135477 : Type'} (a : _135477) : (term74 _135477 a) = (term74 _135477 a).
Proof. exact (eq_refl (term74 _135477 a)). Qed.
Lemma lem7189342 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : (term75 _135477 a x) = (term76 _135477 a).
Proof. exact (MK_COMB (@lem7189341 _135477 a) (@lem7189300 _135477 s x a h1)). Qed.
Lemma lem7189343 {_135477 : Type'} (a : _135477) : (term76 _135477 a) = (term77 _135477 a).
Proof. exact (eq_refl (term76 _135477 a)). Qed.
Lemma lem7189344 {_135477 : Type'} (a : _135477) (x : _135477) : (term78 _135477 a x) = (term78 _135477 a x).
Proof. exact (eq_refl (term78 _135477 a x)). Qed.
Lemma lem7189345 {_135477 : Type'} (x : _135477) (a : _135477) : ((term75 _135477 a x) = (term76 _135477 a)) = ((term75 _135477 a x) = (term77 _135477 a)).
Proof. exact (MK_COMB (@lem7189344 _135477 a x) (@lem7189343 _135477 a)). Qed.
Lemma lem7189346 {_135477 : Type'} (x : _135477) (a : _135477) : (term75 _135477 a x) = (term73 _135477 x a).
Proof. exact (eq_refl (term75 _135477 a x)). Qed.
Lemma lem7189347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7189348 {_135477 : Type'} (x : _135477) (a : _135477) : (term78 _135477 a x) = (term79 _135477 x a).
Proof. exact (MK_COMB (@lem7189347) (@lem7189346 _135477 x a)). Qed.
Lemma lem7189349 {_135477 : Type'} (a : _135477) : (term77 _135477 a) = (term77 _135477 a).
Proof. exact (eq_refl (term77 _135477 a)). Qed.
Lemma lem7189350 {_135477 : Type'} (x : _135477) (a : _135477) : ((term75 _135477 a x) = (term77 _135477 a)) = ((term73 _135477 x a) = (term77 _135477 a)).
Proof. exact (MK_COMB (@lem7189348 _135477 x a) (@lem7189349 _135477 a)). Qed.
Lemma lem7189351 {_135477 : Type'} (x : _135477) (a : _135477) : ((term75 _135477 a x) = (term76 _135477 a)) = ((term73 _135477 x a) = (term77 _135477 a)).
Proof. exact (TRANS (@lem7189345 _135477 x a) (@lem7189350 _135477 x a)). Qed.
Lemma lem7189352 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : (term73 _135477 x a) = (term77 _135477 a).
Proof. exact (EQ_MP (@lem7189351 _135477 x a) (@lem7189342 _135477 s x a h1)). Qed.
Lemma lem7189353 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : term77 _135477 a.
Proof. exact (EQ_MP (@lem7189352 _135477 s x a h1) (@lem7189296 _135477 s x a h1)). Qed.
Lemma lem7189394 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7189395 {_135477 : Type'} (s : _135477 -> Prop) : (term80 _135477 s) = (term80 _135477 s).
Proof. exact (eq_refl (term80 _135477 s)). Qed.
Lemma lem7189396 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term67 _135477 s x a) : (term81 _135477 s x) = (term81 _135477 s a).
Proof. exact (MK_COMB (@lem7189395 _135477 s) (@lem7189304 _135477 s x a h1)). Qed.
Lemma lem7189397 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term81 _135477 s a) = (term72 _135477 s a).
Proof. exact (eq_refl (term81 _135477 s a)). Qed.
Lemma lem7189398 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) : (term82 _135477 s x) = (term82 _135477 s x).
Proof. exact (eq_refl (term82 _135477 s x)). Qed.
Lemma lem7189399 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) : ((term81 _135477 s x) = (term81 _135477 s a)) = ((term81 _135477 s x) = (term72 _135477 s a)).
Proof. exact (MK_COMB (@lem7189398 _135477 s x) (@lem7189397 _135477 s a)). Qed.
Lemma lem7189400 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) : (term81 _135477 s x) = (term72 _135477 s x).
Proof. exact (eq_refl (term81 _135477 s x)). Qed.
Lemma lem7189401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7189402 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) : (term82 _135477 s x) = (term83 _135477 s x).
Proof. exact (MK_COMB (@lem7189401) (@lem7189400 _135477 s x)). Qed.
Lemma lem7189403 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term72 _135477 s a) = (term72 _135477 s a).
Proof. exact (eq_refl (term72 _135477 s a)). Qed.
Lemma lem7189404 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) : ((term81 _135477 s x) = (term72 _135477 s a)) = ((term72 _135477 s x) = (term72 _135477 s a)).
Proof. exact (MK_COMB (@lem7189402 _135477 s x) (@lem7189403 _135477 s a)). Qed.
Lemma lem7189405 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) : ((term81 _135477 s x) = (term81 _135477 s a)) = ((term72 _135477 s x) = (term72 _135477 s a)).
Proof. exact (TRANS (@lem7189399 _135477 x s a) (@lem7189404 _135477 x s a)). Qed.
Lemma lem7189406 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term67 _135477 s x a) : (term72 _135477 s x) = (term72 _135477 s a).
Proof. exact (EQ_MP (@lem7189405 _135477 x s a) (@lem7189396 _135477 s x a h1)). Qed.
Lemma lem7189407 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : term67 _135477 s x a) : term72 _135477 s a.
Proof. exact (EQ_MP (@lem7189406 _135477 s x a h2) (@lem7189306 _135477 s x h1)). Qed.
Lemma lem7189436 {_135477 : Type'} (a : _135477) : (term74 _135477 a) = (term74 _135477 a).
Proof. exact (eq_refl (term74 _135477 a)). Qed.
Lemma lem7189437 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term67 _135477 s x a) : (term75 _135477 a x) = (term76 _135477 a).
Proof. exact (MK_COMB (@lem7189436 _135477 a) (@lem7189310 _135477 s x a h1)). Qed.
Lemma lem7189438 {_135477 : Type'} (a : _135477) : (term76 _135477 a) = (term77 _135477 a).
Proof. exact (eq_refl (term76 _135477 a)). Qed.
Lemma lem7189439 {_135477 : Type'} (a : _135477) (x : _135477) : (term78 _135477 a x) = (term78 _135477 a x).
Proof. exact (eq_refl (term78 _135477 a x)). Qed.
Lemma lem7189440 {_135477 : Type'} (x : _135477) (a : _135477) : ((term75 _135477 a x) = (term76 _135477 a)) = ((term75 _135477 a x) = (term77 _135477 a)).
Proof. exact (MK_COMB (@lem7189439 _135477 a x) (@lem7189438 _135477 a)). Qed.
Lemma lem7189441 {_135477 : Type'} (x : _135477) (a : _135477) : (term75 _135477 a x) = (term73 _135477 x a).
Proof. exact (eq_refl (term75 _135477 a x)). Qed.
Lemma lem7189442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7189443 {_135477 : Type'} (x : _135477) (a : _135477) : (term78 _135477 a x) = (term79 _135477 x a).
Proof. exact (MK_COMB (@lem7189442) (@lem7189441 _135477 x a)). Qed.
Lemma lem7189444 {_135477 : Type'} (a : _135477) : (term77 _135477 a) = (term77 _135477 a).
Proof. exact (eq_refl (term77 _135477 a)). Qed.
Lemma lem7189445 {_135477 : Type'} (x : _135477) (a : _135477) : ((term75 _135477 a x) = (term77 _135477 a)) = ((term73 _135477 x a) = (term77 _135477 a)).
Proof. exact (MK_COMB (@lem7189443 _135477 x a) (@lem7189444 _135477 a)). Qed.
Lemma lem7189446 {_135477 : Type'} (x : _135477) (a : _135477) : ((term75 _135477 a x) = (term76 _135477 a)) = ((term73 _135477 x a) = (term77 _135477 a)).
Proof. exact (TRANS (@lem7189440 _135477 x a) (@lem7189445 _135477 x a)). Qed.
Lemma lem7189447 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term67 _135477 s x a) : (term73 _135477 x a) = (term77 _135477 a).
Proof. exact (EQ_MP (@lem7189446 _135477 x a) (@lem7189437 _135477 s x a h1)). Qed.
Lemma lem7189448 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : term77 _135477 a.
Proof. exact (EQ_MP (@lem7189447 _135477 s x a h2) (@lem7189312 _135477 x a h1)). Qed.
Lemma lem7189464 {_135477 : Type'} (x : _135477) : x = x.
Proof. exact (@lem21386 _135477 x). Qed.
Lemma lem7189465 {_135477 : Type'} (x : _135477) : x = x.
Proof. exact (@lem7189464 _135477 x). Qed.
Lemma lem7189466 {_135477 : Type'} (a : _135477) : a = a.
Proof. exact (@lem7189465 _135477 a). Qed.
Lemma lem7189467 {_135477 : Type'} (a : _135477) : term84 _135477 a.
Proof. exact (fun h0 : term77 _135477 a => @lem7189466 _135477 a). Qed.
Lemma lem7189469 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7189470 {_135477 : Type'} (a : _135477) : (term84 _135477 a) = (a = a).
Proof. exact (@lem7189469 (a = a)). Qed.
Lemma lem7189471 {_135477 : Type'} (a : _135477) : a = a.
Proof. exact (EQ_MP (@lem7189470 _135477 a) (@lem7189467 _135477 a)). Qed.
Lemma lem7189474 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7189476 {_135477 : Type'} (a : _135477) : (term77 _135477 a) = (term86 _135477 a).
Proof. exact (@lem7189474 (a = a)). Qed.
Lemma lem7189479 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : term86 _135477 a.
Proof. exact (EQ_MP (@lem7189476 _135477 a) (@lem7189353 _135477 s x a h1)). Qed.
Lemma lem7189482 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : False.
Proof. exact (@lem7189479 _135477 s x a h1 (@lem7189471 _135477 a)). Qed.
Lemma lem7189483 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : term87.
Proof. exact (fun h0 : ~ False => @lem7189482 _135477 s x a h1). Qed.
Lemma lem7189485 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7189486 : term87 = False.
Proof. exact (@lem7189485 False). Qed.
Lemma lem7189489 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem7189490 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : term88 _135477 s a.
Proof. exact (fun h0 : term72 _135477 s a => @lem7189489 _135477 s a h1). Qed.
Lemma lem7189492 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7189493 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term88 _135477 s a) = (s a).
Proof. exact (@lem7189492 (s a)). Qed.
Lemma lem7189494 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : s a.
Proof. exact (EQ_MP (@lem7189493 _135477 s a) (@lem7189490 _135477 s a h1)). Qed.
Lemma lem7189497 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7189499 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term72 _135477 s a) = (term89 _135477 s a).
Proof. exact (@lem7189497 (s a)). Qed.
Lemma lem7189502 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : term67 _135477 s x a) : term89 _135477 s a.
Proof. exact (EQ_MP (@lem7189499 _135477 s a) (@lem7189407 _135477 s x a h1 h2)). Qed.
Lemma lem7189505 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (@lem7189502 _135477 s x a h1 h3 (@lem7189494 _135477 s a h2)). Qed.
Lemma lem7189506 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : term87.
Proof. exact (fun h0 : ~ False => @lem7189505 _135477 s x a h1 h2 h3). Qed.
Lemma lem7189508 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7189509 : term87 = False.
Proof. exact (@lem7189508 False). Qed.
Lemma lem7189510 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189509) (@lem7189506 _135477 s x a h1 h2 h3)). Qed.
Lemma lem7189526 {_135477 : Type'} (x : _135477) : x = x.
Proof. exact (@lem21386 _135477 x). Qed.
Lemma lem7189527 {_135477 : Type'} (x : _135477) : x = x.
Proof. exact (@lem7189526 _135477 x). Qed.
Lemma lem7189528 {_135477 : Type'} (a : _135477) : a = a.
Proof. exact (@lem7189527 _135477 a). Qed.
Lemma lem7189529 {_135477 : Type'} (a : _135477) : term84 _135477 a.
Proof. exact (fun h0 : term77 _135477 a => @lem7189528 _135477 a). Qed.
Lemma lem7189531 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7189532 {_135477 : Type'} (a : _135477) : (term84 _135477 a) = (a = a).
Proof. exact (@lem7189531 (a = a)). Qed.
Lemma lem7189533 {_135477 : Type'} (a : _135477) : a = a.
Proof. exact (EQ_MP (@lem7189532 _135477 a) (@lem7189529 _135477 a)). Qed.
Lemma lem7189536 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7189538 {_135477 : Type'} (a : _135477) : (term77 _135477 a) = (term86 _135477 a).
Proof. exact (@lem7189536 (a = a)). Qed.
Lemma lem7189541 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : term86 _135477 a.
Proof. exact (EQ_MP (@lem7189538 _135477 a) (@lem7189448 _135477 s x a h1 h2)). Qed.
Lemma lem7189544 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : False.
Proof. exact (@lem7189541 _135477 s x a h1 h2 (@lem7189533 _135477 a)). Qed.
Lemma lem7189545 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : term87.
Proof. exact (fun h0 : ~ False => @lem7189544 _135477 s x a h1 h2). Qed.
Lemma lem7189547 (p : Prop) : (term85 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7189548 : term87 = False.
Proof. exact (@lem7189547 False). Qed.
Lemma lem7189550 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189548) (@lem7189545 _135477 s x a h1 h2)). Qed.
Lemma lem7189551 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem7189510 _135477 s x a h1 h2 h3) (fun h4 : False => @lem7189394 _135477 s a h2)). Qed.
Lemma lem7189553 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189551 _135477 s x a h1 h2 h3) (@lem7189394 _135477 s a h2)). Qed.
Lemma lem7189554 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term71 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189486) (@lem7189483 _135477 s x a h1)). Qed.
Lemma lem7189555 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : (term73 _135477 x a) = False.
Proof. exact (prop_ext (fun h3 : term73 _135477 x a => @lem7189550 _135477 s x a h1 h2) (fun h3 : False => @lem7189312 _135477 x a h1)). Qed.
Lemma lem7189556 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189555 _135477 s x a h1 h2) (@lem7189312 _135477 x a h1)). Qed.
Lemma lem7189557 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : (term72 _135477 s x) = False.
Proof. exact (prop_ext (fun h4 : term72 _135477 s x => @lem7189553 _135477 s x a h1 h2 h3) (fun h4 : False => @lem7189306 _135477 s x h1)). Qed.
Lemma lem7189558 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189557 _135477 s x a h1 h2 h3) (@lem7189306 _135477 s x h1)). Qed.
Lemma lem7189559 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem7189558 _135477 s x a h1 h2 h3) (fun h4 : False => @lem7189302 _135477 s a h2)). Qed.
Lemma lem7189560 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189559 _135477 s x a h1 h2 h3) (@lem7189302 _135477 s a h2)). Qed.
Lemma lem7189561 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : (term73 _135477 x a) = False.
Proof. exact (prop_ext (fun h3 : term73 _135477 x a => @lem7189556 _135477 s x a h1 h2) (fun h3 : False => @lem7189292 _135477 x a h1)). Qed.
Lemma lem7189562 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189561 _135477 s x a h1 h2) (@lem7189292 _135477 x a h1)). Qed.
Lemma lem7189563 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : (term72 _135477 s x) = False.
Proof. exact (prop_ext (fun h4 : term72 _135477 s x => @lem7189560 _135477 s x a h1 h2 h3) (fun h4 : False => @lem7189280 _135477 s x h1)). Qed.
Lemma lem7189564 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189563 _135477 s x a h1 h2 h3) (@lem7189280 _135477 s x h1)). Qed.
Lemma lem7189565 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem7189564 _135477 s x a h1 h2 h3) (fun h4 : False => @lem7189272 _135477 s a h2)). Qed.
Lemma lem7189566 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189565 _135477 s x a h1 h2 h3) (@lem7189272 _135477 s a h2)). Qed.
Lemma lem7189567 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : (term73 _135477 x a) = False.
Proof. exact (prop_ext (fun h3 : term73 _135477 x a => @lem7189562 _135477 s x a h1 h2) (fun h3 : False => @lem7189292 _135477 x a h1)). Qed.
Lemma lem7189568 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term73 _135477 x a) (h2 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189567 _135477 s x a h1 h2) (@lem7189292 _135477 x a h1)). Qed.
Lemma lem7189569 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : (term72 _135477 s x) = False.
Proof. exact (prop_ext (fun h4 : term72 _135477 s x => @lem7189566 _135477 s x a h1 h2 h3) (fun h4 : False => @lem7189280 _135477 s x h1)). Qed.
Lemma lem7189570 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189569 _135477 s x a h1 h2 h3) (@lem7189280 _135477 s x h1)). Qed.
Lemma lem7189571 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem7189570 _135477 s x a h1 h2 h3) (fun h4 : False => @lem7189272 _135477 s a h2)). Qed.
Lemma lem7189572 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : term72 _135477 s x) (h2 : s a) (h3 : term67 _135477 s x a) : False.
Proof. exact (EQ_MP (@lem7189571 _135477 s x a h1 h2 h3) (@lem7189272 _135477 s a h2)). Qed.
Lemma lem7189573 {_135477 : Type'} (s : _135477 -> Prop) (x : _135477) (a : _135477) (h1 : s a) (h2 : term67 _135477 s x a) : False.
Proof. exact (or_elim (@lem7189250 _135477 s x a h2) (fun h0 : term72 _135477 s x => @lem7189572 _135477 s x a h0 h1 h2) (fun h0 : term73 _135477 x a => @lem7189568 _135477 s x a h0 h2)). Qed.
Lemma lem7189574 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : term61 _135477 s x a) (h2 : s a) : False.
Proof. exact (or_elim (@lem7189242 _135477 s x a h1) (fun h0 : term71 _135477 s x a => @lem7189554 _135477 s x a h0) (fun h0 : term67 _135477 s x a => @lem7189573 _135477 s x a h2 h0)). Qed.
Lemma lem7189575 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : term61 _135477 s x a) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem7189574 _135477 x s a h1 h2) (fun h3 : False => @lem7189194 _135477 s a h2)). Qed.
Lemma lem7189576 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : term61 _135477 s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem7189575 _135477 x s a h1 h2) (@lem7189194 _135477 s a h2)). Qed.
Lemma lem7189577 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : term61 _135477 s x a) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem7189576 _135477 x s a h1 h2) (fun h3 : False => @lem7189160 _135477 s a h2)). Qed.
Lemma lem7189578 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : term61 _135477 s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem7189577 _135477 x s a h1 h2) (@lem7189160 _135477 s a h2)). Qed.
Lemma lem7189579 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : term61 _135477 s x a) (h2 : s a) : (term61 _135477 s x a) = False.
Proof. exact (prop_ext (fun h3 : term61 _135477 s x a => @lem7189578 _135477 x s a h1 h2) (fun h3 : False => @lem7189154 _135477 s x a h1)). Qed.
Lemma lem7189580 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : term61 _135477 s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem7189579 _135477 x s a h1 h2) (@lem7189154 _135477 s x a h1)). Qed.
Lemma lem7189581 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : s a) : term60 _135477 s x a.
Proof. exact (fun h0 : term61 _135477 s x a => @lem7189580 _135477 x s a h0 h1). Qed.
Lemma lem7189582 {_135477 : Type'} (x : _135477) (s : _135477 -> Prop) (a : _135477) (h1 : s a) : (term32 _135477 s x a) = (x = a).
Proof. exact (EQ_MP (@lem7189153 _135477 s x a) (@lem7189581 _135477 x s a h1)). Qed.
Lemma lem7189587 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : s a) : term42 _135477 s a.
Proof. exact (fun x : _135477 => @lem7189582 _135477 x s a h1). Qed.
Lemma lem7189588 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term43 _135477 s a.
Proof. exact (fun h0 : s a => @lem7189587 _135477 s a h0). Qed.
Lemma lem7189593 {_135477 : Type'} (a : _135477) : term55 _135477 a.
Proof. exact (fun s : _135477 -> Prop => @lem7189588 _135477 s a). Qed.
Lemma lem7189598 {_135477 : Type'} : term59 _135477.
Proof. exact (fun a : _135477 => @lem7189593 _135477 a). Qed.
Lemma lem7189599 {_135477 : Type'} : term58 _135477.
Proof. exact (EQ_MP (@lem7189148 _135477) (@lem7189598 _135477)). Qed.
Lemma lem7189600 {_135477 : Type'} (a : _135477) : term90 _135477 a.
Proof. exact (@lem7189599 _135477 a). Qed.
Lemma lem7189601 {_135477 : Type'} (a : _135477) : (term90 _135477 a) = (term54 _135477 a).
Proof. exact (eq_refl (term90 _135477 a)). Qed.
Lemma lem7189602 {_135477 : Type'} (a : _135477) : term54 _135477 a.
Proof. exact (EQ_MP (@lem7189601 _135477 a) (@lem7189600 _135477 a)). Qed.
Lemma lem7189603 {_135477 : Type'} (a : _135477) (s : _135477 -> Prop) : term91 _135477 a s.
Proof. exact (@lem7189602 _135477 a s). Qed.
Lemma lem7189604 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : (term91 _135477 a s) = (term45 _135477 s a).
Proof. exact (eq_refl (term91 _135477 a s)). Qed.
Lemma lem7189605 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term45 _135477 s a.
Proof. exact (EQ_MP (@lem7189604 _135477 s a) (@lem7189603 _135477 a s)). Qed.
Lemma lem7189607 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term45 _135477 s a.
Proof. exact (@lem7189059 _135477 s a (@lem7189605 _135477 s a)). Qed.
Lemma lem7189608 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term46 _135477 s a) : False.
Proof. exact (@lem7189607 _135477 s a (@lem7189043 _135477 s a h1)). Qed.
Lemma lem7189609 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term46 _135477 s a) : (term46 _135477 s a) = False.
Proof. exact (prop_ext (fun h2 : term46 _135477 s a => @lem7189608 _135477 s a h1) (fun h2 : False => @lem7189043 _135477 s a h1)). Qed.
Lemma lem7189610 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) (h1 : term46 _135477 s a) : False.
Proof. exact (EQ_MP (@lem7189609 _135477 s a h1) (@lem7189043 _135477 s a h1)). Qed.
Lemma lem7189611 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term45 _135477 s a.
Proof. exact (fun h0 : term46 _135477 s a => @lem7189610 _135477 s a h0). Qed.
Lemma lem7189612 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term43 _135477 s a.
Proof. exact (EQ_MP (@lem7189042 _135477 s a) (@lem7189611 _135477 s a)). Qed.
Lemma lem7189613 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term9 _135477 s a.
Proof. exact (EQ_MP (@lem7189038 _135477 s a) (@lem7189612 _135477 s a)). Qed.
Lemma lem7189614 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term8 _135477 s a.
Proof. exact (EQ_MP (@lem7188951 _135477 s a) (@lem7189613 _135477 s a)). Qed.
Lemma lem7189617 {A : Type'} (s : A -> Prop) (x : A) (h1 : (@DELETE A s x) = (term92 A s x)) : (@DELETE A s x) = (term92 A s x).
Proof. exact (h1). Qed.
Lemma lem7189618 {A : Type'} (s : A -> Prop) (x : A) (h1 : (@DELETE A s x) = (term92 A s x)) : (term92 A s x) = (@DELETE A s x).
Proof. exact (SYM (@lem7189617 A s x h1)). Qed.
Lemma lem7189619 {A : Type'} (s : A -> Prop) (x : A) (h1 : (term92 A s x) = (@DELETE A s x)) : (term92 A s x) = (@DELETE A s x).
Proof. exact (h1). Qed.
Lemma lem7189620 {A : Type'} (s : A -> Prop) (x : A) (h1 : (term92 A s x) = (@DELETE A s x)) : (@DELETE A s x) = (term92 A s x).
Proof. exact (SYM (@lem7189619 A s x h1)). Qed.
Lemma lem7189621 {A : Type'} (s : A -> Prop) (x : A) : ((@DELETE A s x) = (term92 A s x)) = ((term92 A s x) = (@DELETE A s x)).
Proof. exact (prop_ext (fun h1 : (@DELETE A s x) = (term92 A s x) => @lem7189618 A s x h1) (fun h1 : (term92 A s x) = (@DELETE A s x) => @lem7189620 A s x h1)). Qed.
Lemma lem7189622 {A : Type'} (s : A -> Prop) : (term93 A s) = (term94 A s).
Proof. exact (fun_ext (fun x : A => @lem7189621 A s x)). Qed.
Lemma lem7189623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7189624 {A : Type'} (s : A -> Prop) : (term95 A s) = (term96 A s).
Proof. exact (MK_COMB (@lem7189623 A) (@lem7189622 A s)). Qed.
Lemma lem7189625 {A : Type'} : (term97 A) = (term98 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7189624 A s)). Qed.
Lemma lem7189626 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7189627 {A : Type'} : (term99 A) = (term100 A).
Proof. exact (MK_COMB (@lem7189626 A) (@lem7189625 A)). Qed.
Lemma lem7189628 {A : Type'} : term100 A.
Proof. exact (EQ_MP (@lem7189627 A) (@lem3193179 A)). Qed.
Lemma lem7189629 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : term101 _135521 a s) : term101 _135521 a s.
Proof. exact (h1). Qed.
Lemma lem7189630 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : @IN _135521 a s.
Proof. exact (h1). Qed.
Lemma lem7189631 {_135521 : Type'} (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : @FINITE _135521 s.
Proof. exact (h1). Qed.
Lemma lem7189632 {A : Type'} (s : A -> Prop) : term102 A s.
Proof. exact (@lem7188904 A s). Qed.
Lemma lem7189633 {A : Type'} (s : A -> Prop) : (term102 A s) = (term103 A s).
Proof. exact (eq_refl (term102 A s)). Qed.
Lemma lem7189634 {A : Type'} (s : A -> Prop) : term103 A s.
Proof. exact (EQ_MP (@lem7189633 A s) (@lem7189632 A s)). Qed.
Lemma lem7189635 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term104 A s P.
Proof. exact (@lem7189634 A s P). Qed.
Lemma lem7189636 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term104 A s P) = (term105 A s P).
Proof. exact (eq_refl (term104 A s P)). Qed.
Lemma lem7189637 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term105 A s P.
Proof. exact (EQ_MP (@lem7189636 A s P) (@lem7189635 A s P)). Qed.
Lemma lem7189638 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> real) : term106 A s P f.
Proof. exact (@lem7189637 A s P f). Qed.
Lemma lem7189639 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) : (term106 A s P f) = (term107 A f s P).
Proof. exact (eq_refl (term106 A s P f)). Qed.
Lemma lem7189640 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) : term107 A f s P.
Proof. exact (EQ_MP (@lem7189639 A f s P) (@lem7189638 A s P f)). Qed.
Lemma lem7189641 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) (g : A -> real) : term108 A f s P g.
Proof. exact (@lem7189640 A f s P g). Qed.
Lemma lem7189642 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) (g : A -> real) : (term108 A f s P g) = (term109 A f s P g).
Proof. exact (eq_refl (term108 A f s P g)). Qed.
Lemma lem7189643 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) (g : A -> real) : term109 A f s P g.
Proof. exact (EQ_MP (@lem7189642 A f s P g) (@lem7189641 A f s P g)). Qed.
Lemma lem7189644 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7189645 {A : Type'} (f : A -> real) (P : A -> Prop) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term110 A s P f g) = (term111 A f s P g).
Proof. exact (@lem7189643 A f s P g (@lem7189644 A s h1)). Qed.
Lemma lem7189651 {_135521 : Type'} (s : _135521 -> Prop) : (@FINITE _135521 s) = ((@FINITE _135521 s) = True).
Proof. exact (@lem7 (@FINITE _135521 s)). Qed.
Lemma lem7189658 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) (g : A -> real) : term109 A f s P g.
Proof. exact (fun h0 : @FINITE A s => @lem7189645 A f P g s h0). Qed.
Lemma lem7189659 {_135521 : Type'} (f : _135521 -> real) (s : _135521 -> Prop) (P : _135521 -> Prop) (g : _135521 -> real) : term109 _135521 f s P g.
Proof. exact (@lem7189658 _135521 f s P g). Qed.
Lemma lem7189660 {_135521 : Type'} (y : real) (s : _135521 -> Prop) (a : _135521) (f : _135521 -> real) : term112 _135521 y s a f.
Proof. exact (@lem7189659 _135521 (term113 _135521 y) s (term114 _135521 a) f). Qed.
Lemma lem7189661 {_135521 : Type'} (x : _135521) (a : _135521) : (term115 _135521 a x) = (x = a).
Proof. exact (eq_refl (term115 _135521 a x)). Qed.
Lemma lem7189662 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7189663 {_135521 : Type'} (x : _135521) (a : _135521) : (term116 _135521 a x) = (term117 _135521 x a).
Proof. exact (MK_COMB (@lem7189662) (@lem7189661 _135521 x a)). Qed.
Lemma lem7189664 {_135521 : Type'} (x : _135521) (y : real) : (term118 _135521 y x) = y.
Proof. exact (eq_refl (term118 _135521 y x)). Qed.
Lemma lem7189665 {_135521 : Type'} (x : _135521) (a : _135521) (y : real) : (term119 _135521 a y x) = (term120 _135521 x a y).
Proof. exact (MK_COMB (@lem7189663 _135521 x a) (@lem7189664 _135521 x y)). Qed.
Lemma lem7189666 {_135521 : Type'} (f : _135521 -> real) (x : _135521) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem7189667 {_135521 : Type'} (a : _135521) (y : real) (f : _135521 -> real) (x : _135521) : (term121 _135521 a y f x) = (term122 _135521 a y f x).
Proof. exact (MK_COMB (@lem7189665 _135521 x a y) (@lem7189666 _135521 f x)). Qed.
Lemma lem7189668 {_135521 : Type'} (a : _135521) (y : real) (f : _135521 -> real) : (term123 _135521 a y f) = (term124 _135521 a y f).
Proof. exact (fun_ext (fun x : _135521 => @lem7189667 _135521 a y f x)). Qed.
Lemma lem7189669 {_135521 : Type'} (s : _135521 -> Prop) : (@sum _135521 s) = (@sum _135521 s).
Proof. exact (eq_refl (@sum _135521 s)). Qed.
Lemma lem7189670 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) (y : real) (f : _135521 -> real) : (term125 _135521 s a y f) = (term126 _135521 s a y f).
Proof. exact (MK_COMB (@lem7189669 _135521 s) (@lem7189668 _135521 a y f)). Qed.
Lemma lem7189671 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7189672 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) (y : real) (f : _135521 -> real) : (term127 _135521 s a y f) = (term128 _135521 s a y f).
Proof. exact (MK_COMB (@lem7189671) (@lem7189670 _135521 s a y f)). Qed.
Lemma lem7189673 {_135521 : Type'} (x : _135521) (a : _135521) : (term115 _135521 a x) = (x = a).
Proof. exact (eq_refl (term115 _135521 a x)). Qed.
Lemma lem7189674 {_135521 : Type'} (x : _135521) (s : _135521 -> Prop) : (term30 _135521 x s) = (term30 _135521 x s).
Proof. exact (eq_refl (term30 _135521 x s)). Qed.
Lemma lem7189675 {_135521 : Type'} (s : _135521 -> Prop) (x : _135521) (a : _135521) : (term129 _135521 s a x) = (term15 _135521 s x a).
Proof. exact (MK_COMB (@lem7189674 _135521 x s) (@lem7189673 _135521 x a)). Qed.
Lemma lem7189676 {_135521 : Type'} (GEN_PVAR_328 : _135521) : (@SETSPEC _135521 GEN_PVAR_328) = (@SETSPEC _135521 GEN_PVAR_328).
Proof. exact (eq_refl (@SETSPEC _135521 GEN_PVAR_328)). Qed.
Lemma lem7189677 {_135521 : Type'} (GEN_PVAR_328 : _135521) (s : _135521 -> Prop) (x : _135521) (a : _135521) : (term130 _135521 GEN_PVAR_328 s a x) = (term17 _135521 GEN_PVAR_328 s x a).
Proof. exact (MK_COMB (@lem7189676 _135521 GEN_PVAR_328) (@lem7189675 _135521 s x a)). Qed.
Lemma lem7189678 {_135521 : Type'} (x : _135521) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7189679 {_135521 : Type'} (GEN_PVAR_328 : _135521) (s : _135521 -> Prop) (a : _135521) (x : _135521) : (term131 _135521 GEN_PVAR_328 s a x) = (term19 _135521 GEN_PVAR_328 s a x).
Proof. exact (MK_COMB (@lem7189677 _135521 GEN_PVAR_328 s x a) (@lem7189678 _135521 x)). Qed.
Lemma lem7189680 {_135521 : Type'} (GEN_PVAR_328 : _135521) (s : _135521 -> Prop) (a : _135521) : (term132 _135521 GEN_PVAR_328 s a) = (term21 _135521 GEN_PVAR_328 s a).
Proof. exact (fun_ext (fun x : _135521 => @lem7189679 _135521 GEN_PVAR_328 s a x)). Qed.
Lemma lem7189681 {_135521 : Type'} : (@ex _135521) = (@ex _135521).
Proof. exact (eq_refl (@ex _135521)). Qed.
Lemma lem7189682 {_135521 : Type'} (GEN_PVAR_328 : _135521) (s : _135521 -> Prop) (a : _135521) : (term133 _135521 GEN_PVAR_328 s a) = (term23 _135521 GEN_PVAR_328 s a).
Proof. exact (MK_COMB (@lem7189681 _135521) (@lem7189680 _135521 GEN_PVAR_328 s a)). Qed.
Lemma lem7189683 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term134 _135521 s a) = (term25 _135521 s a).
Proof. exact (fun_ext (fun GEN_PVAR_328 : _135521 => @lem7189682 _135521 GEN_PVAR_328 s a)). Qed.
Lemma lem7189684 {_135521 : Type'} : (@GSPEC _135521) = (@GSPEC _135521).
Proof. exact (eq_refl (@GSPEC _135521)). Qed.
Lemma lem7189685 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term135 _135521 s a) = (term5 _135521 s a).
Proof. exact (MK_COMB (@lem7189684 _135521) (@lem7189683 _135521 s a)). Qed.
Lemma lem7189686 {_135521 : Type'} : (@sum _135521) = (@sum _135521).
Proof. exact (eq_refl (@sum _135521)). Qed.
Lemma lem7189687 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term136 _135521 s a) = (term137 _135521 s a).
Proof. exact (MK_COMB (@lem7189686 _135521) (@lem7189685 _135521 s a)). Qed.
Lemma lem7189688 {_135521 : Type'} (y : real) : (term113 _135521 y) = (term113 _135521 y).
Proof. exact (eq_refl (term113 _135521 y)). Qed.
Lemma lem7189689 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) (y : real) : (term138 _135521 s a y) = (term139 _135521 s a y).
Proof. exact (MK_COMB (@lem7189687 _135521 s a) (@lem7189688 _135521 y)). Qed.
Lemma lem7189690 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7189691 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) (y : real) : (term140 _135521 s a y) = (term141 _135521 s a y).
Proof. exact (MK_COMB (@lem7189690) (@lem7189689 _135521 s a y)). Qed.
Lemma lem7189692 {_135521 : Type'} (x : _135521) (a : _135521) : (term115 _135521 a x) = (x = a).
Proof. exact (eq_refl (term115 _135521 a x)). Qed.
Lemma lem7189693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7189694 {_135521 : Type'} (x : _135521) (a : _135521) : (term142 _135521 a x) = (term73 _135521 x a).
Proof. exact (MK_COMB (@lem7189693) (@lem7189692 _135521 x a)). Qed.
Lemma lem7189695 {_135521 : Type'} (x : _135521) (s : _135521 -> Prop) : (term30 _135521 x s) = (term30 _135521 x s).
Proof. exact (eq_refl (term30 _135521 x s)). Qed.
Lemma lem7189696 {_135521 : Type'} (s : _135521 -> Prop) (x : _135521) (a : _135521) : (term143 _135521 s a x) = (term144 _135521 s x a).
Proof. exact (MK_COMB (@lem7189695 _135521 x s) (@lem7189694 _135521 x a)). Qed.
Lemma lem7189697 {_135521 : Type'} (GEN_PVAR_329 : _135521) : (@SETSPEC _135521 GEN_PVAR_329) = (@SETSPEC _135521 GEN_PVAR_329).
Proof. exact (eq_refl (@SETSPEC _135521 GEN_PVAR_329)). Qed.
Lemma lem7189698 {_135521 : Type'} (GEN_PVAR_329 : _135521) (s : _135521 -> Prop) (x : _135521) (a : _135521) : (term145 _135521 GEN_PVAR_329 s a x) = (term146 _135521 GEN_PVAR_329 s x a).
Proof. exact (MK_COMB (@lem7189697 _135521 GEN_PVAR_329) (@lem7189696 _135521 s x a)). Qed.
Lemma lem7189699 {_135521 : Type'} (x : _135521) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7189700 {_135521 : Type'} (GEN_PVAR_329 : _135521) (s : _135521 -> Prop) (a : _135521) (x : _135521) : (term147 _135521 GEN_PVAR_329 s a x) = (term148 _135521 GEN_PVAR_329 s a x).
Proof. exact (MK_COMB (@lem7189698 _135521 GEN_PVAR_329 s x a) (@lem7189699 _135521 x)). Qed.
Lemma lem7189701 {_135521 : Type'} (GEN_PVAR_329 : _135521) (s : _135521 -> Prop) (a : _135521) : (term149 _135521 GEN_PVAR_329 s a) = (term150 _135521 GEN_PVAR_329 s a).
Proof. exact (fun_ext (fun x : _135521 => @lem7189700 _135521 GEN_PVAR_329 s a x)). Qed.
Lemma lem7189702 {_135521 : Type'} : (@ex _135521) = (@ex _135521).
Proof. exact (eq_refl (@ex _135521)). Qed.
Lemma lem7189703 {_135521 : Type'} (GEN_PVAR_329 : _135521) (s : _135521 -> Prop) (a : _135521) : (term151 _135521 GEN_PVAR_329 s a) = (term152 _135521 GEN_PVAR_329 s a).
Proof. exact (MK_COMB (@lem7189702 _135521) (@lem7189701 _135521 GEN_PVAR_329 s a)). Qed.
Lemma lem7189704 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term153 _135521 s a) = (term154 _135521 s a).
Proof. exact (fun_ext (fun GEN_PVAR_329 : _135521 => @lem7189703 _135521 GEN_PVAR_329 s a)). Qed.
Lemma lem7189705 {_135521 : Type'} : (@GSPEC _135521) = (@GSPEC _135521).
Proof. exact (eq_refl (@GSPEC _135521)). Qed.
Lemma lem7189706 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term155 _135521 s a) = (term92 _135521 s a).
Proof. exact (MK_COMB (@lem7189705 _135521) (@lem7189704 _135521 s a)). Qed.
Lemma lem7189707 {_135521 : Type'} : (@sum _135521) = (@sum _135521).
Proof. exact (eq_refl (@sum _135521)). Qed.
Lemma lem7189708 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term156 _135521 s a) = (term157 _135521 s a).
Proof. exact (MK_COMB (@lem7189707 _135521) (@lem7189706 _135521 s a)). Qed.
Lemma lem7189709 {_135521 : Type'} (f : _135521 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7189710 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) (f : _135521 -> real) : (term158 _135521 s a f) = (term159 _135521 s a f).
Proof. exact (MK_COMB (@lem7189708 _135521 s a) (@lem7189709 _135521 f)). Qed.
Lemma lem7189711 {_135521 : Type'} (y : real) (s : _135521 -> Prop) (a : _135521) (f : _135521 -> real) : (term160 _135521 y s a f) = (term161 _135521 y s a f).
Proof. exact (MK_COMB (@lem7189691 _135521 s a y) (@lem7189710 _135521 s a f)). Qed.
Lemma lem7189712 {_135521 : Type'} (y : real) (s : _135521 -> Prop) (a : _135521) (f : _135521 -> real) : ((term125 _135521 s a y f) = (term160 _135521 y s a f)) = ((term126 _135521 s a y f) = (term161 _135521 y s a f)).
Proof. exact (MK_COMB (@lem7189672 _135521 s a y f) (@lem7189711 _135521 y s a f)). Qed.
Lemma lem7189713 {_135521 : Type'} (s : _135521 -> Prop) : (term162 _135521 s) = (term162 _135521 s).
Proof. exact (eq_refl (term162 _135521 s)). Qed.
Lemma lem7189714 {_135521 : Type'} (y : real) (s : _135521 -> Prop) (a : _135521) (f : _135521 -> real) : (term112 _135521 y s a f) = (term163 _135521 y s a f).
Proof. exact (MK_COMB (@lem7189713 _135521 s) (@lem7189712 _135521 y s a f)). Qed.
Lemma lem7189715 {_135521 : Type'} (y : real) (s : _135521 -> Prop) (a : _135521) (f : _135521 -> real) : term163 _135521 y s a f.
Proof. exact (EQ_MP (@lem7189714 _135521 y s a f) (@lem7189660 _135521 y s a f)). Qed.
Lemma lem7189717 {_135521 : Type'} (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : (@FINITE _135521 s) = True.
Proof. exact (EQ_MP (@lem7189651 _135521 s) (@lem7189631 _135521 s h1)). Qed.
Lemma lem7189718 {_135521 : Type'} (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : True = (@FINITE _135521 s).
Proof. exact (SYM (@lem7189717 _135521 s h1)). Qed.
Lemma lem7189719 {_135521 : Type'} (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : @FINITE _135521 s.
Proof. exact (EQ_MP (@lem7189718 _135521 s h1) (@lem0)). Qed.
Lemma lem7189720 {_135521 : Type'} (y : real) (a : _135521) (f : _135521 -> real) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : (term126 _135521 s a y f) = (term161 _135521 y s a f).
Proof. exact (@lem7189715 _135521 y s a f (@lem7189719 _135521 s h1)). Qed.
Lemma lem7189737 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7189738 {_135521 : Type'} (y : real) (a : _135521) (f : _135521 -> real) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : (term128 _135521 s a y f) = (term164 _135521 y s a f).
Proof. exact (MK_COMB (@lem7189737) (@lem7189720 _135521 y a f s h1)). Qed.
Lemma lem7189755 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term165 _135521 s y f a) = (term165 _135521 s y f a).
Proof. exact (eq_refl (term165 _135521 s y f a)). Qed.
Lemma lem7189756 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : ((term126 _135521 s a y f) = (term165 _135521 s y f a)) = ((term161 _135521 y s a f) = (term165 _135521 s y f a)).
Proof. exact (MK_COMB (@lem7189738 _135521 y a f s h1) (@lem7189755 _135521 s y f a)). Qed.
Lemma lem7189775 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : ((term161 _135521 y s a f) = (term165 _135521 s y f a)) = ((term126 _135521 s a y f) = (term165 _135521 s y f a)).
Proof. exact (SYM (@lem7189756 _135521 y f a s h1)). Qed.
Lemma lem7189776 {_132960 : Type'} (f : _132960 -> real) : term166 _132960 f.
Proof. exact (@lem7122619 _132960 f). Qed.
Lemma lem7189777 {_132960 : Type'} (f : _132960 -> real) : (term166 _132960 f) = (term167 _132960 f).
Proof. exact (eq_refl (term166 _132960 f)). Qed.
Lemma lem7189778 {_132960 : Type'} (f : _132960 -> real) : term167 _132960 f.
Proof. exact (EQ_MP (@lem7189777 _132960 f) (@lem7189776 _132960 f)). Qed.
Lemma lem7189779 {_132960 : Type'} (f : _132960 -> real) (s : _132960 -> Prop) : term168 _132960 f s.
Proof. exact (@lem7189778 _132960 f s). Qed.
Lemma lem7189780 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : (term168 _132960 f s) = (term169 _132960 s f).
Proof. exact (eq_refl (term168 _132960 f s)). Qed.
Lemma lem7189781 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : term169 _132960 s f.
Proof. exact (EQ_MP (@lem7189780 _132960 s f) (@lem7189779 _132960 f s)). Qed.
Lemma lem7189782 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : term170 _132960 s f a.
Proof. exact (@lem7189781 _132960 s f a). Qed.
Lemma lem7189783 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : (term170 _132960 s f a) = (term171 _132960 s f a).
Proof. exact (eq_refl (term170 _132960 s f a)). Qed.
Lemma lem7189784 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : term171 _132960 s f a.
Proof. exact (EQ_MP (@lem7189783 _132960 s f a) (@lem7189782 _132960 s f a)). Qed.
Lemma lem7189785 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term101 _132960 a s) : term101 _132960 a s.
Proof. exact (h1). Qed.
Lemma lem7189786 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (h1 : term101 _132960 a s) : (term172 _132960 s a f) = (term173 _132960 s f a).
Proof. exact (@lem7189784 _132960 s f a (@lem7189785 _132960 a s h1)). Qed.
Lemma lem7189792 {A : Type'} (s : A -> Prop) : term174 A s.
Proof. exact (@lem7189628 A s). Qed.
Lemma lem7189793 {A : Type'} (s : A -> Prop) : (term174 A s) = (term96 A s).
Proof. exact (eq_refl (term174 A s)). Qed.
Lemma lem7189794 {A : Type'} (s : A -> Prop) : term96 A s.
Proof. exact (EQ_MP (@lem7189793 A s) (@lem7189792 A s)). Qed.
Lemma lem7189795 {A : Type'} (s : A -> Prop) (x : A) : term175 A s x.
Proof. exact (@lem7189794 A s x). Qed.
Lemma lem7189796 {A : Type'} (s : A -> Prop) (x : A) : (term175 A s x) = ((term92 A s x) = (@DELETE A s x)).
Proof. exact (eq_refl (term175 A s x)). Qed.
Lemma lem7189798 {_135521 : Type'} (s : _135521 -> Prop) : (@FINITE _135521 s) = ((@FINITE _135521 s) = True).
Proof. exact (@lem7 (@FINITE _135521 s)). Qed.
Lemma lem7189800 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) : (@IN _135521 a s) = ((@IN _135521 a s) = True).
Proof. exact (@lem7 (@IN _135521 a s)). Qed.
Lemma lem7189813 {A : Type'} (s : A -> Prop) (x : A) : (term92 A s x) = (@DELETE A s x).
Proof. exact (EQ_MP (@lem7189796 A s x) (@lem7189795 A s x)). Qed.
Lemma lem7189814 {_135521 : Type'} (s : _135521 -> Prop) (x : _135521) : (term92 _135521 s x) = (@DELETE _135521 s x).
Proof. exact (@lem7189813 _135521 s x). Qed.
Lemma lem7189815 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term92 _135521 s a) = (@DELETE _135521 s a).
Proof. exact (@lem7189814 _135521 s a). Qed.
Lemma lem7189818 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term176 _135521 s a) = (term176 _135521 s a).
Proof. exact (eq_refl (term176 _135521 s a)). Qed.
Lemma lem7189819 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term176 _135521 s a) = ((term92 _135521 s a) = (@DELETE _135521 s a)).
Proof. exact (eq_refl (term176 _135521 s a)). Qed.
Lemma lem7189820 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term177 _135521 s a) = (term177 _135521 s a).
Proof. exact (eq_refl (term177 _135521 s a)). Qed.
Lemma lem7189821 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : ((term176 _135521 s a) = (term176 _135521 s a)) = ((term176 _135521 s a) = ((term92 _135521 s a) = (@DELETE _135521 s a))).
Proof. exact (MK_COMB (@lem7189820 _135521 s a) (@lem7189819 _135521 s a)). Qed.
Lemma lem7189822 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term176 _135521 s a) = ((term92 _135521 s a) = (@DELETE _135521 s a)).
Proof. exact (eq_refl (term176 _135521 s a)). Qed.
Lemma lem7189823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7189824 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term177 _135521 s a) = (term178 _135521 s a).
Proof. exact (MK_COMB (@lem7189823) (@lem7189822 _135521 s a)). Qed.
Lemma lem7189825 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : ((term92 _135521 s a) = (@DELETE _135521 s a)) = ((term92 _135521 s a) = (@DELETE _135521 s a)).
Proof. exact (eq_refl ((term92 _135521 s a) = (@DELETE _135521 s a))). Qed.
Lemma lem7189826 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : ((term176 _135521 s a) = ((term92 _135521 s a) = (@DELETE _135521 s a))) = (((term92 _135521 s a) = (@DELETE _135521 s a)) = ((term92 _135521 s a) = (@DELETE _135521 s a))).
Proof. exact (MK_COMB (@lem7189824 _135521 s a) (@lem7189825 _135521 s a)). Qed.
Lemma lem7189827 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : ((term176 _135521 s a) = (term176 _135521 s a)) = (((term92 _135521 s a) = (@DELETE _135521 s a)) = ((term92 _135521 s a) = (@DELETE _135521 s a))).
Proof. exact (TRANS (@lem7189821 _135521 s a) (@lem7189826 _135521 s a)). Qed.
Lemma lem7189828 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : ((term92 _135521 s a) = (@DELETE _135521 s a)) = ((term92 _135521 s a) = (@DELETE _135521 s a)).
Proof. exact (EQ_MP (@lem7189827 _135521 s a) (@lem7189818 _135521 s a)). Qed.
Lemma lem7189829 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term92 _135521 s a) = (@DELETE _135521 s a).
Proof. exact (EQ_MP (@lem7189828 _135521 s a) (@lem7189815 _135521 s a)). Qed.
Lemma lem7189830 {_135521 : Type'} : (@sum _135521) = (@sum _135521).
Proof. exact (eq_refl (@sum _135521)). Qed.
Lemma lem7189831 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : (term157 _135521 s a) = (term179 _135521 s a).
Proof. exact (MK_COMB (@lem7189830 _135521) (@lem7189829 _135521 s a)). Qed.
Lemma lem7189832 {_135521 : Type'} (f : _135521 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7189833 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) (f : _135521 -> real) : (term159 _135521 s a f) = (term172 _135521 s a f).
Proof. exact (MK_COMB (@lem7189831 _135521 s a) (@lem7189832 _135521 f)). Qed.
Lemma lem7189835 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : term171 _132960 s f a.
Proof. exact (fun h0 : term101 _132960 a s => @lem7189786 _132960 f a s h0). Qed.
Lemma lem7189836 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) (a : _135521) : term171 _135521 s f a.
Proof. exact (@lem7189835 _135521 s f a). Qed.
Lemma lem7189840 {_135521 : Type'} (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : (@FINITE _135521 s) = True.
Proof. exact (EQ_MP (@lem7189798 _135521 s) (@lem7189631 _135521 s h1)). Qed.
Lemma lem7189841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7189842 {_135521 : Type'} (s : _135521 -> Prop) (h1 : @FINITE _135521 s) : (term180 _135521 s) = (and True).
Proof. exact (MK_COMB (@lem7189841) (@lem7189840 _135521 s h1)). Qed.
Lemma lem7189844 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (@IN _135521 a s) = True.
Proof. exact (EQ_MP (@lem7189800 _135521 a s) (@lem7189630 _135521 a s h1)). Qed.
Lemma lem7189845 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term101 _135521 a s) = (True /\ True).
Proof. exact (MK_COMB (@lem7189842 _135521 s h1) (@lem7189844 _135521 a s h2)). Qed.
Lemma lem7189847 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7189848 : (True /\ True) = True.
Proof. exact (@lem7189847 True). Qed.
Lemma lem7189849 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term101 _135521 a s) = True.
Proof. exact (TRANS (@lem7189845 _135521 a s h1 h2) (@lem7189848)). Qed.
Lemma lem7189850 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : True = (term101 _135521 a s).
Proof. exact (SYM (@lem7189849 _135521 a s h1 h2)). Qed.
Lemma lem7189851 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : term101 _135521 a s.
Proof. exact (EQ_MP (@lem7189850 _135521 a s h1 h2) (@lem0)). Qed.
Lemma lem7189852 {_135521 : Type'} (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term172 _135521 s a f) = (term173 _135521 s f a).
Proof. exact (@lem7189836 _135521 s f a (@lem7189851 _135521 a s h1 h2)). Qed.
Lemma lem7189853 {_135521 : Type'} (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term159 _135521 s a f) = (term173 _135521 s f a).
Proof. exact (TRANS (@lem7189833 _135521 s a f) (@lem7189852 _135521 f a s h1 h2)). Qed.
Lemma lem7189854 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) (y : real) : (term141 _135521 s a y) = (term141 _135521 s a y).
Proof. exact (eq_refl (term141 _135521 s a y)). Qed.
Lemma lem7189855 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term161 _135521 y s a f) = (term181 _135521 y s f a).
Proof. exact (MK_COMB (@lem7189854 _135521 s a y) (@lem7189853 _135521 f a s h1 h2)). Qed.
Lemma lem7189864 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7189865 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term164 _135521 y s a f) = (term182 _135521 y s f a).
Proof. exact (MK_COMB (@lem7189864) (@lem7189855 _135521 y f a s h1 h2)). Qed.
Lemma lem7189874 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term165 _135521 s y f a) = (term165 _135521 s y f a).
Proof. exact (eq_refl (term165 _135521 s y f a)). Qed.
Lemma lem7189875 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : ((term161 _135521 y s a f) = (term165 _135521 s y f a)) = ((term181 _135521 y s f a) = (term165 _135521 s y f a)).
Proof. exact (MK_COMB (@lem7189865 _135521 y f a s h1 h2) (@lem7189874 _135521 s y f a)). Qed.
Lemma lem7189886 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : ((term181 _135521 y s f a) = (term165 _135521 s y f a)) = ((term161 _135521 y s a f) = (term165 _135521 s y f a)).
Proof. exact (SYM (@lem7189875 _135521 y f a s h1 h2)). Qed.
Lemma lem7189887 {_135477 : Type'} (a : _135477) (s : _135477 -> Prop) (h1 : @IN _135477 a s) : @IN _135477 a s.
Proof. exact (h1). Qed.
Lemma lem7189888 {_135477 : Type'} (a : _135477) (s : _135477 -> Prop) (h1 : @IN _135477 a s) : (term5 _135477 s a) = (@INSERT _135477 a (@EMPTY _135477)).
Proof. exact (@lem7189614 _135477 s a (@lem7189887 _135477 a s h1)). Qed.
Lemma lem7189896 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) : (@IN _135521 a s) = ((@IN _135521 a s) = True).
Proof. exact (@lem7 (@IN _135521 a s)). Qed.
Lemma lem7189901 {_135477 : Type'} (s : _135477 -> Prop) (a : _135477) : term8 _135477 s a.
Proof. exact (fun h0 : @IN _135477 a s => @lem7189888 _135477 a s h0). Qed.
Lemma lem7189902 {_135521 : Type'} (s : _135521 -> Prop) (a : _135521) : term8 _135521 s a.
Proof. exact (@lem7189901 _135521 s a). Qed.
Lemma lem7189904 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (@IN _135521 a s) = True.
Proof. exact (EQ_MP (@lem7189896 _135521 a s) (@lem7189630 _135521 a s h1)). Qed.
Lemma lem7189905 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : True = (@IN _135521 a s).
Proof. exact (SYM (@lem7189904 _135521 a s h1)). Qed.
Lemma lem7189906 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : @IN _135521 a s.
Proof. exact (EQ_MP (@lem7189905 _135521 a s h1) (@lem0)). Qed.
Lemma lem7189907 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (term5 _135521 s a) = (@INSERT _135521 a (@EMPTY _135521)).
Proof. exact (@lem7189902 _135521 s a (@lem7189906 _135521 a s h1)). Qed.
Lemma lem7189908 {_135521 : Type'} : (@sum _135521) = (@sum _135521).
Proof. exact (eq_refl (@sum _135521)). Qed.
Lemma lem7189909 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (term137 _135521 s a) = (term183 _135521 a).
Proof. exact (MK_COMB (@lem7189908 _135521) (@lem7189907 _135521 a s h1)). Qed.
Lemma lem7189910 {_135521 : Type'} (y : real) : (term113 _135521 y) = (term113 _135521 y).
Proof. exact (eq_refl (term113 _135521 y)). Qed.
Lemma lem7189911 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (term139 _135521 s a y) = (term184 _135521 a y).
Proof. exact (MK_COMB (@lem7189909 _135521 a s h1) (@lem7189910 _135521 y)). Qed.
Lemma lem7189912 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7189913 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (term141 _135521 s a y) = (term185 _135521 a y).
Proof. exact (MK_COMB (@lem7189912) (@lem7189911 _135521 y a s h1)). Qed.
Lemma lem7189914 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) (a : _135521) : (term173 _135521 s f a) = (term173 _135521 s f a).
Proof. exact (eq_refl (term173 _135521 s f a)). Qed.
Lemma lem7189915 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (term181 _135521 y s f a) = (term186 _135521 y s f a).
Proof. exact (MK_COMB (@lem7189913 _135521 y a s h1) (@lem7189914 _135521 s f a)). Qed.
Lemma lem7189916 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7189917 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (term182 _135521 y s f a) = (term187 _135521 y s f a).
Proof. exact (MK_COMB (@lem7189916) (@lem7189915 _135521 y f a s h1)). Qed.
Lemma lem7189918 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term165 _135521 s y f a) = (term165 _135521 s y f a).
Proof. exact (eq_refl (term165 _135521 s y f a)). Qed.
Lemma lem7189919 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : ((term181 _135521 y s f a) = (term165 _135521 s y f a)) = ((term186 _135521 y s f a) = (term165 _135521 s y f a)).
Proof. exact (MK_COMB (@lem7189917 _135521 y f a s h1) (@lem7189918 _135521 s y f a)). Qed.
Lemma lem7189922 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : ((term186 _135521 y s f a) = (term165 _135521 s y f a)) = ((term181 _135521 y s f a) = (term165 _135521 s y f a)).
Proof. exact (SYM (@lem7189919 _135521 y f a s h1)). Qed.
Lemma lem7189926 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term3 _133036 x f) = (f x).
Proof. exact (EQ_MP (@lem7188909 _133036 f x) (@lem7188908 _133036 f x)). Qed.
Lemma lem7189927 {_135521 : Type'} (f : _135521 -> real) (x : _135521) : (term3 _135521 x f) = (f x).
Proof. exact (@lem7189926 _135521 f x). Qed.
Lemma lem7189928 {_135521 : Type'} (y : real) (a : _135521) : (term184 _135521 a y) = (term118 _135521 y a).
Proof. exact (@lem7189927 _135521 (term113 _135521 y) a). Qed.
Lemma lem7189930 {A B : Type'} (f : A -> B) (y : A) : (term188 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7189931 {_135521 : Type'} (f : _135521 -> real) (y : _135521) : (term189 _135521 f y) = (f y).
Proof. exact (@lem7189930 _135521 real f y). Qed.
Lemma lem7189932 {_135521 : Type'} (y : real) (a : _135521) : (term190 _135521 y a) = (term118 _135521 y a).
Proof. exact (@lem7189931 _135521 (term113 _135521 y) a). Qed.
Lemma lem7189933 {_135521 : Type'} (x : _135521) (y : real) : (term118 _135521 y x) = y.
Proof. exact (eq_refl (term118 _135521 y x)). Qed.
Lemma lem7189934 {_135521 : Type'} (y : real) : (term191 _135521 y) = (term113 _135521 y).
Proof. exact (fun_ext (fun x : _135521 => @lem7189933 _135521 x y)). Qed.
Lemma lem7189935 {_135521 : Type'} (a : _135521) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7189936 {_135521 : Type'} (y : real) (a : _135521) : (term190 _135521 y a) = (term118 _135521 y a).
Proof. exact (MK_COMB (@lem7189934 _135521 y) (@lem7189935 _135521 a)). Qed.
Lemma lem7189937 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7189938 {_135521 : Type'} (y : real) (a : _135521) : (term192 _135521 y a) = (term193 _135521 y a).
Proof. exact (MK_COMB (@lem7189937) (@lem7189936 _135521 y a)). Qed.
Lemma lem7189939 {_135521 : Type'} (a : _135521) (y : real) : (term118 _135521 y a) = y.
Proof. exact (eq_refl (term118 _135521 y a)). Qed.
Lemma lem7189940 {_135521 : Type'} (a : _135521) (y : real) : ((term190 _135521 y a) = (term118 _135521 y a)) = ((term118 _135521 y a) = y).
Proof. exact (MK_COMB (@lem7189938 _135521 y a) (@lem7189939 _135521 a y)). Qed.
Lemma lem7189941 {_135521 : Type'} (a : _135521) (y : real) : (term118 _135521 y a) = y.
Proof. exact (EQ_MP (@lem7189940 _135521 a y) (@lem7189932 _135521 y a)). Qed.
Lemma lem7189942 {_135521 : Type'} (a : _135521) (y : real) : (term184 _135521 a y) = y.
Proof. exact (TRANS (@lem7189928 _135521 y a) (@lem7189941 _135521 a y)). Qed.
Lemma lem7189943 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7189944 {_135521 : Type'} (a : _135521) (y : real) : (term185 _135521 a y) = (real_add y).
Proof. exact (MK_COMB (@lem7189943) (@lem7189942 _135521 a y)). Qed.
Lemma lem7189945 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) (a : _135521) : (term173 _135521 s f a) = (term173 _135521 s f a).
Proof. exact (eq_refl (term173 _135521 s f a)). Qed.
Lemma lem7189946 {_135521 : Type'} (y : real) (s : _135521 -> Prop) (f : _135521 -> real) (a : _135521) : (term186 _135521 y s f a) = (term194 _135521 y s f a).
Proof. exact (MK_COMB (@lem7189944 _135521 a y) (@lem7189945 _135521 s f a)). Qed.
Lemma lem7189947 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7189948 {_135521 : Type'} (y : real) (s : _135521 -> Prop) (f : _135521 -> real) (a : _135521) : (term187 _135521 y s f a) = (term195 _135521 y s f a).
Proof. exact (MK_COMB (@lem7189947) (@lem7189946 _135521 y s f a)). Qed.
Lemma lem7189949 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term165 _135521 s y f a) = (term165 _135521 s y f a).
Proof. exact (eq_refl (term165 _135521 s y f a)). Qed.
Lemma lem7189950 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : ((term186 _135521 y s f a) = (term165 _135521 s y f a)) = ((term194 _135521 y s f a) = (term165 _135521 s y f a)).
Proof. exact (MK_COMB (@lem7189948 _135521 y s f a) (@lem7189949 _135521 s y f a)). Qed.
Lemma lem7189953 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : ((term194 _135521 y s f a) = (term165 _135521 s y f a)) = ((term186 _135521 y s f a) = (term165 _135521 s y f a)).
Proof. exact (SYM (@lem7189950 _135521 s y f a)). Qed.
Lemma lem7189964 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term196 _135521 s y f a) = (term197 _135521 s y f a).
Proof. exact (@lem1988318 (term194 _135521 y s f a) (term165 _135521 s y f a)). Qed.
Lemma lem7189977 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) : (term198 _135521 y f a) = (term199 _135521 y f a).
Proof. exact (@lem1982792 y (f a)). Qed.
Lemma lem7189980 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) : (term200 _135521 s f) = (term200 _135521 s f).
Proof. exact (eq_refl (term200 _135521 s f)). Qed.
Lemma lem7189981 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term165 _135521 s y f a) = (term201 _135521 s y f a).
Proof. exact (MK_COMB (@lem7189980 _135521 s f) (@lem7189977 _135521 y f a)). Qed.
Lemma lem7189982 {_135521 : Type'} (y : real) (s : _135521 -> Prop) (f : _135521 -> real) (a : _135521) : (term201 _135521 s y f a) = (term202 _135521 y s f a).
Proof. exact (@lem1982757 y (@sum _135521 s f) (term203 _135521 f a)). Qed.
Lemma lem7189983 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term204 _135521 s f a) = (term205 _135521 a s f).
Proof. exact (@lem1982761 (term203 _135521 f a) (@sum _135521 s f)). Qed.
Lemma lem7189984 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem7189985 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term202 _135521 y s f a) = (term206 _135521 y a s f).
Proof. exact (MK_COMB (@lem7189984 y) (@lem7189983 _135521 a s f)). Qed.
Lemma lem7189986 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term201 _135521 s y f a) = (term206 _135521 y a s f).
Proof. exact (TRANS (@lem7189982 _135521 y s f a) (@lem7189985 _135521 y a s f)). Qed.
Lemma lem7189987 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term165 _135521 s y f a) = (term206 _135521 y a s f).
Proof. exact (TRANS (@lem7189981 _135521 s y f a) (@lem7189986 _135521 y a s f)). Qed.
Lemma lem7189993 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) (a : _135521) : (term173 _135521 s f a) = (term204 _135521 s f a).
Proof. exact (@lem1982792 (@sum _135521 s f) (f a)). Qed.
Lemma lem7189998 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term204 _135521 s f a) = (term205 _135521 a s f).
Proof. exact (@lem1982761 (term203 _135521 f a) (@sum _135521 s f)). Qed.
Lemma lem7190000 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term173 _135521 s f a) = (term205 _135521 a s f).
Proof. exact (TRANS (@lem7189993 _135521 s f a) (@lem7189998 _135521 a s f)). Qed.
Lemma lem7190003 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem7190006 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term194 _135521 y s f a) = (term206 _135521 y a s f).
Proof. exact (MK_COMB (@lem7190003 y) (@lem7190000 _135521 a s f)). Qed.
Lemma lem7190007 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7190008 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term207 _135521 y s f a) = (term208 _135521 y a s f).
Proof. exact (MK_COMB (@lem7190007) (@lem7190006 _135521 y a s f)). Qed.
Lemma lem7190009 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term209 _135521 s y f a) = (term210 _135521 y a s f).
Proof. exact (MK_COMB (@lem7190008 _135521 y a s f) (@lem7189987 _135521 y a s f)). Qed.
Lemma lem7190010 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term210 _135521 y a s f) = (term211 _135521 y a s f).
Proof. exact (@lem1982792 (term206 _135521 y a s f) (term206 _135521 y a s f)). Qed.
Lemma lem7190011 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term212 _135521 y a s f) = (term213 _135521 y a s f).
Proof. exact (@lem1982781 y term214 (term205 _135521 a s f)). Qed.
Lemma lem7190012 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term215 _135521 a s f) = (term216 _135521 a s f).
Proof. exact (@lem1982781 (term203 _135521 f a) term214 (@sum _135521 s f)). Qed.
Lemma lem7190013 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) : (term217 _135521 s f) = (term217 _135521 s f).
Proof. exact (eq_refl (term217 _135521 s f)). Qed.
Lemma lem7190014 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term218 _135521 f a) = (term219 _135521 f a).
Proof. exact (@lem1982749 term214 term214 (f a)). Qed.
Lemma lem7190016 (x : nat) : (term220 x) = (term221 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7190017 : term214 = term222.
Proof. exact (@lem7190016 term223). Qed.
Lemma lem7190019 (x : nat) : (term220 x) = (term221 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7190020 : term214 = term222.
Proof. exact (@lem7190019 term223). Qed.
Lemma lem7190021 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190022 : term224 = term225.
Proof. exact (MK_COMB (@lem7190021) (@lem7190020)). Qed.
Lemma lem7190023 : term226 = term227.
Proof. exact (MK_COMB (@lem7190022) (@lem7190017)). Qed.
Lemma lem7190024 : term227 = term228.
Proof. exact (@lem1981613 term214 term214 term229 term229). Qed.
Lemma lem7190026 (m : nat) (n : nat) : (term230 m n) = (term231 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7190027 : term232 = term233.
Proof. exact (@lem7190026 term223 term223). Qed.
Lemma lem7190028 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190029 : term235 = term223.
Proof. exact (EQ_MP (@lem7190028) (@lem940073)). Qed.
Lemma lem7190030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190031 : term233 = term229.
Proof. exact (MK_COMB (@lem7190030) (@lem7190029)). Qed.
Lemma lem7190032 : term232 = term229.
Proof. exact (TRANS (@lem7190027) (@lem7190031)). Qed.
Lemma lem7190034 (m : nat) (n : nat) : (term236 m n) = (term231 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7190035 : term226 = term233.
Proof. exact (@lem7190034 term223 term223). Qed.
Lemma lem7190036 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190037 : term235 = term223.
Proof. exact (EQ_MP (@lem7190036) (@lem940073)). Qed.
Lemma lem7190038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190039 : term233 = term229.
Proof. exact (MK_COMB (@lem7190038) (@lem7190037)). Qed.
Lemma lem7190040 : term226 = term229.
Proof. exact (TRANS (@lem7190035) (@lem7190039)). Qed.
Lemma lem7190041 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7190042 : term237 = term238.
Proof. exact (MK_COMB (@lem7190041) (@lem7190040)). Qed.
Lemma lem7190043 : term228 = term239.
Proof. exact (MK_COMB (@lem7190042) (@lem7190032)). Qed.
Lemma lem7190044 : term227 = term239.
Proof. exact (TRANS (@lem7190024) (@lem7190043)). Qed.
Lemma lem7190045 : term226 = term239.
Proof. exact (TRANS (@lem7190023) (@lem7190044)). Qed.
Lemma lem7190047 (x : real) : (term240 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7190048 : term239 = term229.
Proof. exact (@lem7190047 term229). Qed.
Lemma lem7190049 : term226 = term229.
Proof. exact (TRANS (@lem7190045) (@lem7190048)). Qed.
Lemma lem7190050 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190051 : term241 = term242.
Proof. exact (MK_COMB (@lem7190050) (@lem7190049)). Qed.
Lemma lem7190052 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem7190053 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term219 _135521 f a) = (term243 _135521 f a).
Proof. exact (MK_COMB (@lem7190051) (@lem7190052 _135521 f a)). Qed.
Lemma lem7190054 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term218 _135521 f a) = (term243 _135521 f a).
Proof. exact (TRANS (@lem7190014 _135521 f a) (@lem7190053 _135521 f a)). Qed.
Lemma lem7190055 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term243 _135521 f a) = (f a).
Proof. exact (@lem1982709 (f a)). Qed.
Lemma lem7190056 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term218 _135521 f a) = (f a).
Proof. exact (TRANS (@lem7190054 _135521 f a) (@lem7190055 _135521 f a)). Qed.
Lemma lem7190057 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190058 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term244 _135521 f a) = (term245 _135521 f a).
Proof. exact (MK_COMB (@lem7190057) (@lem7190056 _135521 f a)). Qed.
Lemma lem7190059 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term216 _135521 a s f) = (term246 _135521 a s f).
Proof. exact (MK_COMB (@lem7190058 _135521 f a) (@lem7190013 _135521 s f)). Qed.
Lemma lem7190060 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term215 _135521 a s f) = (term246 _135521 a s f).
Proof. exact (TRANS (@lem7190012 _135521 a s f) (@lem7190059 _135521 a s f)). Qed.
Lemma lem7190063 (y : real) : (term247 y) = (term247 y).
Proof. exact (eq_refl (term247 y)). Qed.
Lemma lem7190064 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term213 _135521 y a s f) = (term248 _135521 y a s f).
Proof. exact (MK_COMB (@lem7190063 y) (@lem7190060 _135521 a s f)). Qed.
Lemma lem7190065 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term212 _135521 y a s f) = (term248 _135521 y a s f).
Proof. exact (TRANS (@lem7190011 _135521 y a s f) (@lem7190064 _135521 y a s f)). Qed.
Lemma lem7190066 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term249 _135521 y a s f) = (term249 _135521 y a s f).
Proof. exact (eq_refl (term249 _135521 y a s f)). Qed.
Lemma lem7190067 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term211 _135521 y a s f) = (term250 _135521 y a s f).
Proof. exact (MK_COMB (@lem7190066 _135521 y a s f) (@lem7190065 _135521 y a s f)). Qed.
Lemma lem7190068 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term250 _135521 y a s f) = (term251 _135521 y a s f).
Proof. exact (@lem1982753 y (term252 y) (term205 _135521 a s f) (term246 _135521 a s f)). Qed.
Lemma lem7190069 (y : real) : (term253 y) = (term254 y).
Proof. exact (@lem1982715 term214 y). Qed.
Lemma lem7190071 (x : nat) : (real_of_num x) = (term255 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7190072 : term229 = term239.
Proof. exact (@lem7190071 term223). Qed.
Lemma lem7190074 (x : nat) : (term220 x) = (term221 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7190075 : term214 = term222.
Proof. exact (@lem7190074 term223). Qed.
Lemma lem7190076 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190077 : term256 = term257.
Proof. exact (MK_COMB (@lem7190076) (@lem7190075)). Qed.
Lemma lem7190078 : term258 = term259.
Proof. exact (MK_COMB (@lem7190077) (@lem7190072)). Qed.
Lemma lem7190079 : term260.
Proof. exact (@lem1981473 term214 term229 term229 term229 term261 term229). Qed.
Lemma lem7190081 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190082 : term263 = term264.
Proof. exact (@lem7190081 (NUMERAL 0) term223). Qed.
Lemma lem7190083 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190084 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190085 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190084 h1) (fun h1 : term264 = True => @lem7190083)). Qed.
Lemma lem7190086 : term264 = True.
Proof. exact (EQ_MP (@lem7190085) (@lem7190083)). Qed.
Lemma lem7190087 : term263 = True.
Proof. exact (TRANS (@lem7190082) (@lem7190086)). Qed.
Lemma lem7190088 : True = term263.
Proof. exact (SYM (@lem7190087)). Qed.
Lemma lem7190089 : term263.
Proof. exact (EQ_MP (@lem7190088) (@lem0)). Qed.
Lemma lem7190090 : term266.
Proof. exact (@lem7190079 (@lem7190089)). Qed.
Lemma lem7190092 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190093 : term263 = term264.
Proof. exact (@lem7190092 (NUMERAL 0) term223). Qed.
Lemma lem7190094 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190095 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190096 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190095 h1) (fun h1 : term264 = True => @lem7190094)). Qed.
Lemma lem7190097 : term264 = True.
Proof. exact (EQ_MP (@lem7190096) (@lem7190094)). Qed.
Lemma lem7190098 : term263 = True.
Proof. exact (TRANS (@lem7190093) (@lem7190097)). Qed.
Lemma lem7190099 : True = term263.
Proof. exact (SYM (@lem7190098)). Qed.
Lemma lem7190100 : term263.
Proof. exact (EQ_MP (@lem7190099) (@lem0)). Qed.
Lemma lem7190101 : term267.
Proof. exact (@lem7190090 (@lem7190100)). Qed.
Lemma lem7190103 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190104 : term263 = term264.
Proof. exact (@lem7190103 (NUMERAL 0) term223). Qed.
Lemma lem7190105 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190106 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190107 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190106 h1) (fun h1 : term264 = True => @lem7190105)). Qed.
Lemma lem7190108 : term264 = True.
Proof. exact (EQ_MP (@lem7190107) (@lem7190105)). Qed.
Lemma lem7190109 : term263 = True.
Proof. exact (TRANS (@lem7190104) (@lem7190108)). Qed.
Lemma lem7190110 : True = term263.
Proof. exact (SYM (@lem7190109)). Qed.
Lemma lem7190111 : term263.
Proof. exact (EQ_MP (@lem7190110) (@lem0)). Qed.
Lemma lem7190112 : term268.
Proof. exact (@lem7190101 (@lem7190111)). Qed.
Lemma lem7190114 (m : nat) (n : nat) : (term230 m n) = (term231 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7190115 : term232 = term233.
Proof. exact (@lem7190114 term223 term223). Qed.
Lemma lem7190116 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190117 : term235 = term223.
Proof. exact (EQ_MP (@lem7190116) (@lem940073)). Qed.
Lemma lem7190118 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190119 : term233 = term229.
Proof. exact (MK_COMB (@lem7190118) (@lem7190117)). Qed.
Lemma lem7190120 : term232 = term229.
Proof. exact (TRANS (@lem7190115) (@lem7190119)). Qed.
Lemma lem7190122 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7190123 : term271 = term272.
Proof. exact (@lem7190122 term223 term223). Qed.
Lemma lem7190124 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190125 : term235 = term223.
Proof. exact (EQ_MP (@lem7190124) (@lem940073)). Qed.
Lemma lem7190126 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190127 : term233 = term229.
Proof. exact (MK_COMB (@lem7190126) (@lem7190125)). Qed.
Lemma lem7190128 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7190129 : term272 = term214.
Proof. exact (MK_COMB (@lem7190128) (@lem7190127)). Qed.
Lemma lem7190130 : term271 = term214.
Proof. exact (TRANS (@lem7190123) (@lem7190129)). Qed.
Lemma lem7190131 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190132 : term273 = term256.
Proof. exact (MK_COMB (@lem7190131) (@lem7190130)). Qed.
Lemma lem7190133 : term274 = term258.
Proof. exact (MK_COMB (@lem7190132) (@lem7190120)). Qed.
Lemma lem7190135 (m : nat) : (term275 m) = term261.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7190136 : term258 = term261.
Proof. exact (@lem7190135 term223). Qed.
Lemma lem7190137 : term274 = term261.
Proof. exact (TRANS (@lem7190133) (@lem7190136)). Qed.
Lemma lem7190138 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190139 : term276 = term277.
Proof. exact (MK_COMB (@lem7190138) (@lem7190137)). Qed.
Lemma lem7190140 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem7190141 : term278 = term279.
Proof. exact (MK_COMB (@lem7190139) (@lem7190140)). Qed.
Lemma lem7190143 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190144 : term279 = term261.
Proof. exact (@lem7190143 term223). Qed.
Lemma lem7190145 : term278 = term261.
Proof. exact (TRANS (@lem7190141) (@lem7190144)). Qed.
Lemma lem7190147 (m : nat) (n : nat) : (term230 m n) = (term231 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7190148 : term232 = term233.
Proof. exact (@lem7190147 term223 term223). Qed.
Lemma lem7190149 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190150 : term235 = term223.
Proof. exact (EQ_MP (@lem7190149) (@lem940073)). Qed.
Lemma lem7190151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190152 : term233 = term229.
Proof. exact (MK_COMB (@lem7190151) (@lem7190150)). Qed.
Lemma lem7190153 : term232 = term229.
Proof. exact (TRANS (@lem7190148) (@lem7190152)). Qed.
Lemma lem7190154 : term277 = term277.
Proof. exact (eq_refl term277). Qed.
Lemma lem7190155 : term281 = term279.
Proof. exact (MK_COMB (@lem7190154) (@lem7190153)). Qed.
Lemma lem7190157 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190158 : term279 = term261.
Proof. exact (@lem7190157 term223). Qed.
Lemma lem7190159 : term281 = term261.
Proof. exact (TRANS (@lem7190155) (@lem7190158)). Qed.
Lemma lem7190160 : term261 = term281.
Proof. exact (SYM (@lem7190159)). Qed.
Lemma lem7190161 : term278 = term281.
Proof. exact (TRANS (@lem7190145) (@lem7190160)). Qed.
Lemma lem7190162 : term259 = term282.
Proof. exact (@lem7190112 (@lem7190161)). Qed.
Lemma lem7190163 : term258 = term282.
Proof. exact (TRANS (@lem7190078) (@lem7190162)). Qed.
Lemma lem7190165 (x : real) : (term240 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7190166 : term282 = term261.
Proof. exact (@lem7190165 term261). Qed.
Lemma lem7190167 : term258 = term261.
Proof. exact (TRANS (@lem7190163) (@lem7190166)). Qed.
Lemma lem7190168 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190169 : term283 = term277.
Proof. exact (MK_COMB (@lem7190168) (@lem7190167)). Qed.
Lemma lem7190170 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7190171 (y : real) : (term254 y) = (term284 y).
Proof. exact (MK_COMB (@lem7190169) (@lem7190170 y)). Qed.
Lemma lem7190172 (y : real) : (term253 y) = (term284 y).
Proof. exact (TRANS (@lem7190069 y) (@lem7190171 y)). Qed.
Lemma lem7190173 (y : real) : (term284 y) = term261.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7190174 (y : real) : (term253 y) = term261.
Proof. exact (TRANS (@lem7190172 y) (@lem7190173 y)). Qed.
Lemma lem7190175 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190176 (y : real) : (term285 y) = term286.
Proof. exact (MK_COMB (@lem7190175) (@lem7190174 y)). Qed.
Lemma lem7190177 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term287 _135521 a s f) = (term288 _135521 a s f).
Proof. exact (@lem1982753 (term203 _135521 f a) (f a) (@sum _135521 s f) (term217 _135521 s f)). Qed.
Lemma lem7190178 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term289 _135521 f a) = (term290 _135521 f a).
Proof. exact (@lem1982713 term214 (f a)). Qed.
Lemma lem7190180 (x : nat) : (real_of_num x) = (term255 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7190181 : term229 = term239.
Proof. exact (@lem7190180 term223). Qed.
Lemma lem7190183 (x : nat) : (term220 x) = (term221 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7190184 : term214 = term222.
Proof. exact (@lem7190183 term223). Qed.
Lemma lem7190185 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190186 : term256 = term257.
Proof. exact (MK_COMB (@lem7190185) (@lem7190184)). Qed.
Lemma lem7190187 : term258 = term259.
Proof. exact (MK_COMB (@lem7190186) (@lem7190181)). Qed.
Lemma lem7190188 : term260.
Proof. exact (@lem1981473 term214 term229 term229 term229 term261 term229). Qed.
Lemma lem7190190 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190191 : term263 = term264.
Proof. exact (@lem7190190 (NUMERAL 0) term223). Qed.
Lemma lem7190192 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190193 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190194 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190193 h1) (fun h1 : term264 = True => @lem7190192)). Qed.
Lemma lem7190195 : term264 = True.
Proof. exact (EQ_MP (@lem7190194) (@lem7190192)). Qed.
Lemma lem7190196 : term263 = True.
Proof. exact (TRANS (@lem7190191) (@lem7190195)). Qed.
Lemma lem7190197 : True = term263.
Proof. exact (SYM (@lem7190196)). Qed.
Lemma lem7190198 : term263.
Proof. exact (EQ_MP (@lem7190197) (@lem0)). Qed.
Lemma lem7190199 : term266.
Proof. exact (@lem7190188 (@lem7190198)). Qed.
Lemma lem7190201 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190202 : term263 = term264.
Proof. exact (@lem7190201 (NUMERAL 0) term223). Qed.
Lemma lem7190203 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190204 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190205 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190204 h1) (fun h1 : term264 = True => @lem7190203)). Qed.
Lemma lem7190206 : term264 = True.
Proof. exact (EQ_MP (@lem7190205) (@lem7190203)). Qed.
Lemma lem7190207 : term263 = True.
Proof. exact (TRANS (@lem7190202) (@lem7190206)). Qed.
Lemma lem7190208 : True = term263.
Proof. exact (SYM (@lem7190207)). Qed.
Lemma lem7190209 : term263.
Proof. exact (EQ_MP (@lem7190208) (@lem0)). Qed.
Lemma lem7190210 : term267.
Proof. exact (@lem7190199 (@lem7190209)). Qed.
Lemma lem7190212 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190213 : term263 = term264.
Proof. exact (@lem7190212 (NUMERAL 0) term223). Qed.
Lemma lem7190214 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190215 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190216 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190215 h1) (fun h1 : term264 = True => @lem7190214)). Qed.
Lemma lem7190217 : term264 = True.
Proof. exact (EQ_MP (@lem7190216) (@lem7190214)). Qed.
Lemma lem7190218 : term263 = True.
Proof. exact (TRANS (@lem7190213) (@lem7190217)). Qed.
Lemma lem7190219 : True = term263.
Proof. exact (SYM (@lem7190218)). Qed.
Lemma lem7190220 : term263.
Proof. exact (EQ_MP (@lem7190219) (@lem0)). Qed.
Lemma lem7190221 : term268.
Proof. exact (@lem7190210 (@lem7190220)). Qed.
Lemma lem7190223 (m : nat) (n : nat) : (term230 m n) = (term231 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7190224 : term232 = term233.
Proof. exact (@lem7190223 term223 term223). Qed.
Lemma lem7190225 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190226 : term235 = term223.
Proof. exact (EQ_MP (@lem7190225) (@lem940073)). Qed.
Lemma lem7190227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190228 : term233 = term229.
Proof. exact (MK_COMB (@lem7190227) (@lem7190226)). Qed.
Lemma lem7190229 : term232 = term229.
Proof. exact (TRANS (@lem7190224) (@lem7190228)). Qed.
Lemma lem7190231 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7190232 : term271 = term272.
Proof. exact (@lem7190231 term223 term223). Qed.
Lemma lem7190233 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190234 : term235 = term223.
Proof. exact (EQ_MP (@lem7190233) (@lem940073)). Qed.
Lemma lem7190235 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190236 : term233 = term229.
Proof. exact (MK_COMB (@lem7190235) (@lem7190234)). Qed.
Lemma lem7190237 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7190238 : term272 = term214.
Proof. exact (MK_COMB (@lem7190237) (@lem7190236)). Qed.
Lemma lem7190239 : term271 = term214.
Proof. exact (TRANS (@lem7190232) (@lem7190238)). Qed.
Lemma lem7190240 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190241 : term273 = term256.
Proof. exact (MK_COMB (@lem7190240) (@lem7190239)). Qed.
Lemma lem7190242 : term274 = term258.
Proof. exact (MK_COMB (@lem7190241) (@lem7190229)). Qed.
Lemma lem7190244 (m : nat) : (term275 m) = term261.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7190245 : term258 = term261.
Proof. exact (@lem7190244 term223). Qed.
Lemma lem7190246 : term274 = term261.
Proof. exact (TRANS (@lem7190242) (@lem7190245)). Qed.
Lemma lem7190247 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190248 : term276 = term277.
Proof. exact (MK_COMB (@lem7190247) (@lem7190246)). Qed.
Lemma lem7190249 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem7190250 : term278 = term279.
Proof. exact (MK_COMB (@lem7190248) (@lem7190249)). Qed.
Lemma lem7190252 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190253 : term279 = term261.
Proof. exact (@lem7190252 term223). Qed.
Lemma lem7190254 : term278 = term261.
Proof. exact (TRANS (@lem7190250) (@lem7190253)). Qed.
Lemma lem7190256 (m : nat) (n : nat) : (term230 m n) = (term231 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7190257 : term232 = term233.
Proof. exact (@lem7190256 term223 term223). Qed.
Lemma lem7190258 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190259 : term235 = term223.
Proof. exact (EQ_MP (@lem7190258) (@lem940073)). Qed.
Lemma lem7190260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190261 : term233 = term229.
Proof. exact (MK_COMB (@lem7190260) (@lem7190259)). Qed.
Lemma lem7190262 : term232 = term229.
Proof. exact (TRANS (@lem7190257) (@lem7190261)). Qed.
Lemma lem7190263 : term277 = term277.
Proof. exact (eq_refl term277). Qed.
Lemma lem7190264 : term281 = term279.
Proof. exact (MK_COMB (@lem7190263) (@lem7190262)). Qed.
Lemma lem7190266 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190267 : term279 = term261.
Proof. exact (@lem7190266 term223). Qed.
Lemma lem7190268 : term281 = term261.
Proof. exact (TRANS (@lem7190264) (@lem7190267)). Qed.
Lemma lem7190269 : term261 = term281.
Proof. exact (SYM (@lem7190268)). Qed.
Lemma lem7190270 : term278 = term281.
Proof. exact (TRANS (@lem7190254) (@lem7190269)). Qed.
Lemma lem7190271 : term259 = term282.
Proof. exact (@lem7190221 (@lem7190270)). Qed.
Lemma lem7190272 : term258 = term282.
Proof. exact (TRANS (@lem7190187) (@lem7190271)). Qed.
Lemma lem7190274 (x : real) : (term240 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7190275 : term282 = term261.
Proof. exact (@lem7190274 term261). Qed.
Lemma lem7190276 : term258 = term261.
Proof. exact (TRANS (@lem7190272) (@lem7190275)). Qed.
Lemma lem7190277 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190278 : term283 = term277.
Proof. exact (MK_COMB (@lem7190277) (@lem7190276)). Qed.
Lemma lem7190279 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem7190280 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term290 _135521 f a) = (term291 _135521 f a).
Proof. exact (MK_COMB (@lem7190278) (@lem7190279 _135521 f a)). Qed.
Lemma lem7190281 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term289 _135521 f a) = (term291 _135521 f a).
Proof. exact (TRANS (@lem7190178 _135521 f a) (@lem7190280 _135521 f a)). Qed.
Lemma lem7190282 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term291 _135521 f a) = term261.
Proof. exact (@lem1982719 (f a)). Qed.
Lemma lem7190283 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term289 _135521 f a) = term261.
Proof. exact (TRANS (@lem7190281 _135521 f a) (@lem7190282 _135521 f a)). Qed.
Lemma lem7190284 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190285 {_135521 : Type'} (f : _135521 -> real) (a : _135521) : (term292 _135521 f a) = term286.
Proof. exact (MK_COMB (@lem7190284) (@lem7190283 _135521 f a)). Qed.
Lemma lem7190286 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) : (term293 _135521 s f) = (term294 _135521 s f).
Proof. exact (@lem1982715 term214 (@sum _135521 s f)). Qed.
Lemma lem7190288 (x : nat) : (real_of_num x) = (term255 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7190289 : term229 = term239.
Proof. exact (@lem7190288 term223). Qed.
Lemma lem7190291 (x : nat) : (term220 x) = (term221 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7190292 : term214 = term222.
Proof. exact (@lem7190291 term223). Qed.
Lemma lem7190293 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190294 : term256 = term257.
Proof. exact (MK_COMB (@lem7190293) (@lem7190292)). Qed.
Lemma lem7190295 : term258 = term259.
Proof. exact (MK_COMB (@lem7190294) (@lem7190289)). Qed.
Lemma lem7190296 : term260.
Proof. exact (@lem1981473 term214 term229 term229 term229 term261 term229). Qed.
Lemma lem7190298 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190299 : term263 = term264.
Proof. exact (@lem7190298 (NUMERAL 0) term223). Qed.
Lemma lem7190300 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190301 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190302 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190301 h1) (fun h1 : term264 = True => @lem7190300)). Qed.
Lemma lem7190303 : term264 = True.
Proof. exact (EQ_MP (@lem7190302) (@lem7190300)). Qed.
Lemma lem7190304 : term263 = True.
Proof. exact (TRANS (@lem7190299) (@lem7190303)). Qed.
Lemma lem7190305 : True = term263.
Proof. exact (SYM (@lem7190304)). Qed.
Lemma lem7190306 : term263.
Proof. exact (EQ_MP (@lem7190305) (@lem0)). Qed.
Lemma lem7190307 : term266.
Proof. exact (@lem7190296 (@lem7190306)). Qed.
Lemma lem7190309 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190310 : term263 = term264.
Proof. exact (@lem7190309 (NUMERAL 0) term223). Qed.
Lemma lem7190311 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190312 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190313 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190312 h1) (fun h1 : term264 = True => @lem7190311)). Qed.
Lemma lem7190314 : term264 = True.
Proof. exact (EQ_MP (@lem7190313) (@lem7190311)). Qed.
Lemma lem7190315 : term263 = True.
Proof. exact (TRANS (@lem7190310) (@lem7190314)). Qed.
Lemma lem7190316 : True = term263.
Proof. exact (SYM (@lem7190315)). Qed.
Lemma lem7190317 : term263.
Proof. exact (EQ_MP (@lem7190316) (@lem0)). Qed.
Lemma lem7190318 : term267.
Proof. exact (@lem7190307 (@lem7190317)). Qed.
Lemma lem7190320 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190321 : term263 = term264.
Proof. exact (@lem7190320 (NUMERAL 0) term223). Qed.
Lemma lem7190322 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190323 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190324 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190323 h1) (fun h1 : term264 = True => @lem7190322)). Qed.
Lemma lem7190325 : term264 = True.
Proof. exact (EQ_MP (@lem7190324) (@lem7190322)). Qed.
Lemma lem7190326 : term263 = True.
Proof. exact (TRANS (@lem7190321) (@lem7190325)). Qed.
Lemma lem7190327 : True = term263.
Proof. exact (SYM (@lem7190326)). Qed.
Lemma lem7190328 : term263.
Proof. exact (EQ_MP (@lem7190327) (@lem0)). Qed.
Lemma lem7190329 : term268.
Proof. exact (@lem7190318 (@lem7190328)). Qed.
Lemma lem7190331 (m : nat) (n : nat) : (term230 m n) = (term231 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7190332 : term232 = term233.
Proof. exact (@lem7190331 term223 term223). Qed.
Lemma lem7190333 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190334 : term235 = term223.
Proof. exact (EQ_MP (@lem7190333) (@lem940073)). Qed.
Lemma lem7190335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190336 : term233 = term229.
Proof. exact (MK_COMB (@lem7190335) (@lem7190334)). Qed.
Lemma lem7190337 : term232 = term229.
Proof. exact (TRANS (@lem7190332) (@lem7190336)). Qed.
Lemma lem7190339 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7190340 : term271 = term272.
Proof. exact (@lem7190339 term223 term223). Qed.
Lemma lem7190341 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190342 : term235 = term223.
Proof. exact (EQ_MP (@lem7190341) (@lem940073)). Qed.
Lemma lem7190343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190344 : term233 = term229.
Proof. exact (MK_COMB (@lem7190343) (@lem7190342)). Qed.
Lemma lem7190345 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7190346 : term272 = term214.
Proof. exact (MK_COMB (@lem7190345) (@lem7190344)). Qed.
Lemma lem7190347 : term271 = term214.
Proof. exact (TRANS (@lem7190340) (@lem7190346)). Qed.
Lemma lem7190348 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7190349 : term273 = term256.
Proof. exact (MK_COMB (@lem7190348) (@lem7190347)). Qed.
Lemma lem7190350 : term274 = term258.
Proof. exact (MK_COMB (@lem7190349) (@lem7190337)). Qed.
Lemma lem7190352 (m : nat) : (term275 m) = term261.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7190353 : term258 = term261.
Proof. exact (@lem7190352 term223). Qed.
Lemma lem7190354 : term274 = term261.
Proof. exact (TRANS (@lem7190350) (@lem7190353)). Qed.
Lemma lem7190355 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190356 : term276 = term277.
Proof. exact (MK_COMB (@lem7190355) (@lem7190354)). Qed.
Lemma lem7190357 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem7190358 : term278 = term279.
Proof. exact (MK_COMB (@lem7190356) (@lem7190357)). Qed.
Lemma lem7190360 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190361 : term279 = term261.
Proof. exact (@lem7190360 term223). Qed.
Lemma lem7190362 : term278 = term261.
Proof. exact (TRANS (@lem7190358) (@lem7190361)). Qed.
Lemma lem7190364 (m : nat) (n : nat) : (term230 m n) = (term231 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7190365 : term232 = term233.
Proof. exact (@lem7190364 term223 term223). Qed.
Lemma lem7190366 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190367 : term235 = term223.
Proof. exact (EQ_MP (@lem7190366) (@lem940073)). Qed.
Lemma lem7190368 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190369 : term233 = term229.
Proof. exact (MK_COMB (@lem7190368) (@lem7190367)). Qed.
Lemma lem7190370 : term232 = term229.
Proof. exact (TRANS (@lem7190365) (@lem7190369)). Qed.
Lemma lem7190371 : term277 = term277.
Proof. exact (eq_refl term277). Qed.
Lemma lem7190372 : term281 = term279.
Proof. exact (MK_COMB (@lem7190371) (@lem7190370)). Qed.
Lemma lem7190374 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190375 : term279 = term261.
Proof. exact (@lem7190374 term223). Qed.
Lemma lem7190376 : term281 = term261.
Proof. exact (TRANS (@lem7190372) (@lem7190375)). Qed.
Lemma lem7190377 : term261 = term281.
Proof. exact (SYM (@lem7190376)). Qed.
Lemma lem7190378 : term278 = term281.
Proof. exact (TRANS (@lem7190362) (@lem7190377)). Qed.
Lemma lem7190379 : term259 = term282.
Proof. exact (@lem7190329 (@lem7190378)). Qed.
Lemma lem7190380 : term258 = term282.
Proof. exact (TRANS (@lem7190295) (@lem7190379)). Qed.
Lemma lem7190382 (x : real) : (term240 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7190383 : term282 = term261.
Proof. exact (@lem7190382 term261). Qed.
Lemma lem7190384 : term258 = term261.
Proof. exact (TRANS (@lem7190380) (@lem7190383)). Qed.
Lemma lem7190385 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190386 : term283 = term277.
Proof. exact (MK_COMB (@lem7190385) (@lem7190384)). Qed.
Lemma lem7190387 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) : (@sum _135521 s f) = (@sum _135521 s f).
Proof. exact (eq_refl (@sum _135521 s f)). Qed.
Lemma lem7190388 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) : (term294 _135521 s f) = (term295 _135521 s f).
Proof. exact (MK_COMB (@lem7190386) (@lem7190387 _135521 s f)). Qed.
Lemma lem7190389 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) : (term293 _135521 s f) = (term295 _135521 s f).
Proof. exact (TRANS (@lem7190286 _135521 s f) (@lem7190388 _135521 s f)). Qed.
Lemma lem7190390 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) : (term295 _135521 s f) = term261.
Proof. exact (@lem1982719 (@sum _135521 s f)). Qed.
Lemma lem7190391 {_135521 : Type'} (s : _135521 -> Prop) (f : _135521 -> real) : (term293 _135521 s f) = term261.
Proof. exact (TRANS (@lem7190389 _135521 s f) (@lem7190390 _135521 s f)). Qed.
Lemma lem7190392 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term288 _135521 a s f) = term296.
Proof. exact (MK_COMB (@lem7190285 _135521 f a) (@lem7190391 _135521 s f)). Qed.
Lemma lem7190393 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term287 _135521 a s f) = term296.
Proof. exact (TRANS (@lem7190177 _135521 a s f) (@lem7190392 _135521 a s f)). Qed.
Lemma lem7190394 : term296 = term261.
Proof. exact (@lem1982721 term261). Qed.
Lemma lem7190395 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term287 _135521 a s f) = term261.
Proof. exact (TRANS (@lem7190393 _135521 a s f) (@lem7190394)). Qed.
Lemma lem7190396 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term251 _135521 y a s f) = term296.
Proof. exact (MK_COMB (@lem7190176 y) (@lem7190395 _135521 a s f)). Qed.
Lemma lem7190397 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term250 _135521 y a s f) = term296.
Proof. exact (TRANS (@lem7190068 _135521 y a s f) (@lem7190396 _135521 y a s f)). Qed.
Lemma lem7190398 : term296 = term261.
Proof. exact (@lem1982721 term261). Qed.
Lemma lem7190399 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term250 _135521 y a s f) = term261.
Proof. exact (TRANS (@lem7190397 _135521 y a s f) (@lem7190398)). Qed.
Lemma lem7190400 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term211 _135521 y a s f) = term261.
Proof. exact (TRANS (@lem7190067 _135521 y a s f) (@lem7190399 _135521 y a s f)). Qed.
Lemma lem7190401 {_135521 : Type'} (y : real) (a : _135521) (s : _135521 -> Prop) (f : _135521 -> real) : (term210 _135521 y a s f) = term261.
Proof. exact (TRANS (@lem7190010 _135521 y a s f) (@lem7190400 _135521 y a s f)). Qed.
Lemma lem7190402 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term209 _135521 s y f a) = term261.
Proof. exact (TRANS (@lem7190009 _135521 y a s f) (@lem7190401 _135521 y a s f)). Qed.
Lemma lem7190403 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7190404 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term297 _135521 s y f a) = term298.
Proof. exact (MK_COMB (@lem7190403) (@lem7190402 _135521 s y f a)). Qed.
Lemma lem7190405 : term298 = term299.
Proof. exact (@lem1982785 term261). Qed.
Lemma lem7190407 (x : nat) : (real_of_num x) = (term255 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7190408 : term261 = term282.
Proof. exact (@lem7190407 (NUMERAL 0)). Qed.
Lemma lem7190410 (x : nat) : (term220 x) = (term221 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7190411 : term214 = term222.
Proof. exact (@lem7190410 term223). Qed.
Lemma lem7190412 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7190413 : term224 = term225.
Proof. exact (MK_COMB (@lem7190412) (@lem7190411)). Qed.
Lemma lem7190414 : term299 = term300.
Proof. exact (MK_COMB (@lem7190413) (@lem7190408)). Qed.
Lemma lem7190415 : term300 = term301.
Proof. exact (@lem1981613 term214 term261 term229 term229). Qed.
Lemma lem7190417 (m : nat) (n : nat) : (term230 m n) = (term231 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7190418 : term232 = term233.
Proof. exact (@lem7190417 term223 term223). Qed.
Lemma lem7190419 : (term234 = (BIT1 0)) = (term235 = term223).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7190420 : term235 = term223.
Proof. exact (EQ_MP (@lem7190419) (@lem940073)). Qed.
Lemma lem7190421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7190422 : term233 = term229.
Proof. exact (MK_COMB (@lem7190421) (@lem7190420)). Qed.
Lemma lem7190423 : term232 = term229.
Proof. exact (TRANS (@lem7190418) (@lem7190422)). Qed.
Lemma lem7190425 (x : nat) : (term302 x) = term261.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7190426 : term299 = term261.
Proof. exact (@lem7190425 term223). Qed.
Lemma lem7190427 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7190428 : term303 = term304.
Proof. exact (MK_COMB (@lem7190427) (@lem7190426)). Qed.
Lemma lem7190429 : term301 = term282.
Proof. exact (MK_COMB (@lem7190428) (@lem7190423)). Qed.
Lemma lem7190430 : term300 = term282.
Proof. exact (TRANS (@lem7190415) (@lem7190429)). Qed.
Lemma lem7190431 : term299 = term282.
Proof. exact (TRANS (@lem7190414) (@lem7190430)). Qed.
Lemma lem7190433 (x : real) : (term240 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7190434 : term282 = term261.
Proof. exact (@lem7190433 term261). Qed.
Lemma lem7190435 : term299 = term261.
Proof. exact (TRANS (@lem7190431) (@lem7190434)). Qed.
Lemma lem7190436 : term298 = term261.
Proof. exact (TRANS (@lem7190405) (@lem7190435)). Qed.
Lemma lem7190437 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term305 _135521 s y f a) = (term305 _135521 s y f a).
Proof. exact (eq_refl (term305 _135521 s y f a)). Qed.
Lemma lem7190438 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : ((term297 _135521 s y f a) = term298) = ((term297 _135521 s y f a) = term261).
Proof. exact (MK_COMB (@lem7190437 _135521 s y f a) (@lem7190436)). Qed.
Lemma lem7190439 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term297 _135521 s y f a) = term261.
Proof. exact (EQ_MP (@lem7190438 _135521 s y f a) (@lem7190404 _135521 s y f a)). Qed.
Lemma lem7190440 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7190441 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term306 _135521 s y f a) = term307.
Proof. exact (MK_COMB (@lem7190440) (@lem7190439 _135521 s y f a)). Qed.
Lemma lem7190442 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem7190443 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term308 _135521 s y f a) = term309.
Proof. exact (MK_COMB (@lem7190441 _135521 s y f a) (@lem7190442)). Qed.
Lemma lem7190444 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7190445 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term310 _135521 s y f a) = term307.
Proof. exact (MK_COMB (@lem7190444) (@lem7190402 _135521 s y f a)). Qed.
Lemma lem7190446 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem7190447 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term311 _135521 s y f a) = term309.
Proof. exact (MK_COMB (@lem7190445 _135521 s y f a) (@lem7190446)). Qed.
Lemma lem7190448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7190449 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term312 _135521 s y f a) = term313.
Proof. exact (MK_COMB (@lem7190448) (@lem7190447 _135521 s y f a)). Qed.
Lemma lem7190450 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term197 _135521 s y f a) = term314.
Proof. exact (MK_COMB (@lem7190449 _135521 s y f a) (@lem7190443 _135521 s y f a)). Qed.
Lemma lem7190464 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term196 _135521 s y f a) = term314.
Proof. exact (TRANS (@lem7189964 _135521 s y f a) (@lem7190450 _135521 s y f a)). Qed.
Lemma lem7190474 (h1 : term314) : term314.
Proof. exact (h1). Qed.
Lemma lem7190475 (h1 : term309) : term309.
Proof. exact (h1). Qed.
Lemma lem7190477 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7190478 : term309 = term315.
Proof. exact (@lem7190477 term261 term261). Qed.
Lemma lem7190480 (x : nat) : (real_of_num x) = (term255 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7190481 : term261 = term282.
Proof. exact (@lem7190480 (NUMERAL 0)). Qed.
Lemma lem7190483 (x : nat) : (real_of_num x) = (term255 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7190484 : term261 = term282.
Proof. exact (@lem7190483 (NUMERAL 0)). Qed.
Lemma lem7190485 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7190486 : term316 = term317.
Proof. exact (MK_COMB (@lem7190485) (@lem7190484)). Qed.
Lemma lem7190487 : term315 = term318.
Proof. exact (MK_COMB (@lem7190486) (@lem7190481)). Qed.
Lemma lem7190488 : term319.
Proof. exact (@lem1980255 term261 term229 term261 term229). Qed.
Lemma lem7190490 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190491 : term263 = term264.
Proof. exact (@lem7190490 (NUMERAL 0) term223). Qed.
Lemma lem7190492 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190493 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190494 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190493 h1) (fun h1 : term264 = True => @lem7190492)). Qed.
Lemma lem7190495 : term264 = True.
Proof. exact (EQ_MP (@lem7190494) (@lem7190492)). Qed.
Lemma lem7190496 : term263 = True.
Proof. exact (TRANS (@lem7190491) (@lem7190495)). Qed.
Lemma lem7190497 : True = term263.
Proof. exact (SYM (@lem7190496)). Qed.
Lemma lem7190498 : term263.
Proof. exact (EQ_MP (@lem7190497) (@lem0)). Qed.
Lemma lem7190499 : term320.
Proof. exact (@lem7190488 (@lem7190498)). Qed.
Lemma lem7190501 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190502 : term263 = term264.
Proof. exact (@lem7190501 (NUMERAL 0) term223). Qed.
Lemma lem7190503 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190504 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190505 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190504 h1) (fun h1 : term264 = True => @lem7190503)). Qed.
Lemma lem7190506 : term264 = True.
Proof. exact (EQ_MP (@lem7190505) (@lem7190503)). Qed.
Lemma lem7190507 : term263 = True.
Proof. exact (TRANS (@lem7190502) (@lem7190506)). Qed.
Lemma lem7190508 : True = term263.
Proof. exact (SYM (@lem7190507)). Qed.
Lemma lem7190509 : term263.
Proof. exact (EQ_MP (@lem7190508) (@lem0)). Qed.
Lemma lem7190510 : term318 = term321.
Proof. exact (@lem7190499 (@lem7190509)). Qed.
Lemma lem7190512 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190513 : term279 = term261.
Proof. exact (@lem7190512 term223). Qed.
Lemma lem7190515 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190516 : term279 = term261.
Proof. exact (@lem7190515 term223). Qed.
Lemma lem7190517 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7190518 : term322 = term316.
Proof. exact (MK_COMB (@lem7190517) (@lem7190516)). Qed.
Lemma lem7190519 : term321 = term315.
Proof. exact (MK_COMB (@lem7190518) (@lem7190513)). Qed.
Lemma lem7190521 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190522 : term315 = term323.
Proof. exact (@lem7190521 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7190523 : term323 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7190524 : term315 = False.
Proof. exact (TRANS (@lem7190522) (@lem7190523)). Qed.
Lemma lem7190525 : term321 = False.
Proof. exact (TRANS (@lem7190519) (@lem7190524)). Qed.
Lemma lem7190526 : term318 = False.
Proof. exact (TRANS (@lem7190510) (@lem7190525)). Qed.
Lemma lem7190527 : term315 = False.
Proof. exact (TRANS (@lem7190487) (@lem7190526)). Qed.
Lemma lem7190528 : term309 = False.
Proof. exact (TRANS (@lem7190478) (@lem7190527)). Qed.
Lemma lem7190529 (h1 : term309) : False.
Proof. exact (EQ_MP (@lem7190528) (@lem7190475 h1)). Qed.
Lemma lem7190530 (h1 : term309) : term309.
Proof. exact (h1). Qed.
Lemma lem7190532 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7190533 : term309 = term315.
Proof. exact (@lem7190532 term261 term261). Qed.
Lemma lem7190535 (x : nat) : (real_of_num x) = (term255 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7190536 : term261 = term282.
Proof. exact (@lem7190535 (NUMERAL 0)). Qed.
Lemma lem7190538 (x : nat) : (real_of_num x) = (term255 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7190539 : term261 = term282.
Proof. exact (@lem7190538 (NUMERAL 0)). Qed.
Lemma lem7190540 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7190541 : term316 = term317.
Proof. exact (MK_COMB (@lem7190540) (@lem7190539)). Qed.
Lemma lem7190542 : term315 = term318.
Proof. exact (MK_COMB (@lem7190541) (@lem7190536)). Qed.
Lemma lem7190543 : term319.
Proof. exact (@lem1980255 term261 term229 term261 term229). Qed.
Lemma lem7190545 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190546 : term263 = term264.
Proof. exact (@lem7190545 (NUMERAL 0) term223). Qed.
Lemma lem7190547 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190548 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190549 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190548 h1) (fun h1 : term264 = True => @lem7190547)). Qed.
Lemma lem7190550 : term264 = True.
Proof. exact (EQ_MP (@lem7190549) (@lem7190547)). Qed.
Lemma lem7190551 : term263 = True.
Proof. exact (TRANS (@lem7190546) (@lem7190550)). Qed.
Lemma lem7190552 : True = term263.
Proof. exact (SYM (@lem7190551)). Qed.
Lemma lem7190553 : term263.
Proof. exact (EQ_MP (@lem7190552) (@lem0)). Qed.
Lemma lem7190554 : term320.
Proof. exact (@lem7190543 (@lem7190553)). Qed.
Lemma lem7190556 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190557 : term263 = term264.
Proof. exact (@lem7190556 (NUMERAL 0) term223). Qed.
Lemma lem7190558 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7190559 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7190560 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem7190559 h1) (fun h1 : term264 = True => @lem7190558)). Qed.
Lemma lem7190561 : term264 = True.
Proof. exact (EQ_MP (@lem7190560) (@lem7190558)). Qed.
Lemma lem7190562 : term263 = True.
Proof. exact (TRANS (@lem7190557) (@lem7190561)). Qed.
Lemma lem7190563 : True = term263.
Proof. exact (SYM (@lem7190562)). Qed.
Lemma lem7190564 : term263.
Proof. exact (EQ_MP (@lem7190563) (@lem0)). Qed.
Lemma lem7190565 : term318 = term321.
Proof. exact (@lem7190554 (@lem7190564)). Qed.
Lemma lem7190567 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190568 : term279 = term261.
Proof. exact (@lem7190567 term223). Qed.
Lemma lem7190570 (x : nat) : (term280 x) = term261.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7190571 : term279 = term261.
Proof. exact (@lem7190570 term223). Qed.
Lemma lem7190572 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7190573 : term322 = term316.
Proof. exact (MK_COMB (@lem7190572) (@lem7190571)). Qed.
Lemma lem7190574 : term321 = term315.
Proof. exact (MK_COMB (@lem7190573) (@lem7190568)). Qed.
Lemma lem7190576 (m : nat) (n : nat) : (term262 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7190577 : term315 = term323.
Proof. exact (@lem7190576 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7190578 : term323 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7190579 : term315 = False.
Proof. exact (TRANS (@lem7190577) (@lem7190578)). Qed.
Lemma lem7190580 : term321 = False.
Proof. exact (TRANS (@lem7190574) (@lem7190579)). Qed.
Lemma lem7190581 : term318 = False.
Proof. exact (TRANS (@lem7190565) (@lem7190580)). Qed.
Lemma lem7190582 : term315 = False.
Proof. exact (TRANS (@lem7190542) (@lem7190581)). Qed.
Lemma lem7190583 : term309 = False.
Proof. exact (TRANS (@lem7190533) (@lem7190582)). Qed.
Lemma lem7190584 (h1 : term309) : False.
Proof. exact (EQ_MP (@lem7190583) (@lem7190530 h1)). Qed.
Lemma lem7190585 (h1 : term314) : False.
Proof. exact (or_elim (@lem7190474 h1) (fun h0 : term309 => @lem7190529 h0) (fun h0 : term309 => @lem7190584 h0)). Qed.
Lemma lem7190587 (h1 : term314) : term314.
Proof. exact (h1). Qed.
Lemma lem7190588 (h1 : term314) : term314 = False.
Proof. exact (prop_ext (fun h2 : term314 => @lem7190585 h1) (fun h2 : False => @lem7190587 h1)). Qed.
Lemma lem7190589 (h1 : term314) : False.
Proof. exact (EQ_MP (@lem7190588 h1) (@lem7190587 h1)). Qed.
Lemma lem7190590 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) (h1 : term196 _135521 s y f a) : term196 _135521 s y f a.
Proof. exact (h1). Qed.
Lemma lem7190591 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) (h1 : term196 _135521 s y f a) : term314.
Proof. exact (EQ_MP (@lem7190464 _135521 s y f a) (@lem7190590 _135521 s y f a h1)). Qed.
Lemma lem7190592 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) (h1 : term196 _135521 s y f a) : term314 = False.
Proof. exact (prop_ext (fun h2 : term314 => @lem7190589 h2) (fun h2 : False => @lem7190591 _135521 s y f a h1)). Qed.
Lemma lem7190593 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) (h1 : term196 _135521 s y f a) : False.
Proof. exact (EQ_MP (@lem7190592 _135521 s y f a h1) (@lem7190591 _135521 s y f a h1)). Qed.
Lemma lem7190594 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : term324 _135521 s y f a.
Proof. exact (fun h0 : term196 _135521 s y f a => @lem7190593 _135521 s y f a h0). Qed.
Lemma lem7190595 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : term325 _135521 s y f a.
Proof. exact (@lem1386578 ((term194 _135521 y s f a) = (term165 _135521 s y f a))). Qed.
Lemma lem7190598 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term194 _135521 y s f a) = (term165 _135521 s y f a).
Proof. exact (@lem7190595 _135521 s y f a (@lem7190594 _135521 s y f a)). Qed.
Lemma lem7190599 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : (term186 _135521 y s f a) = (term165 _135521 s y f a).
Proof. exact (EQ_MP (@lem7189953 _135521 s y f a) (@lem7190598 _135521 s y f a)). Qed.
Lemma lem7190600 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @IN _135521 a s) : (term181 _135521 y s f a) = (term165 _135521 s y f a).
Proof. exact (EQ_MP (@lem7189922 _135521 y f a s h1) (@lem7190599 _135521 s y f a)). Qed.
Lemma lem7190601 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term161 _135521 y s a f) = (term165 _135521 s y f a).
Proof. exact (EQ_MP (@lem7189886 _135521 y f a s h1 h2) (@lem7190600 _135521 y f a s h2)). Qed.
Lemma lem7190602 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term126 _135521 s a y f) = (term165 _135521 s y f a).
Proof. exact (EQ_MP (@lem7189775 _135521 y f a s h1) (@lem7190601 _135521 y f a s h1 h2)). Qed.
Lemma lem7190603 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : term101 _135521 a s) : @IN _135521 a s.
Proof. exact (proj2 (@lem7189629 _135521 a s h1)). Qed.
Lemma lem7190604 {_135521 : Type'} (a : _135521) (s : _135521 -> Prop) (h1 : term101 _135521 a s) : @FINITE _135521 s.
Proof. exact (proj1 (@lem7189629 _135521 a s h1)). Qed.
Lemma lem7190605 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (@IN _135521 a s) = ((term126 _135521 s a y f) = (term165 _135521 s y f a)).
Proof. exact (prop_ext (fun h3 : @IN _135521 a s => @lem7190602 _135521 y f a s h1 h2) (fun h3 : (term126 _135521 s a y f) = (term165 _135521 s y f a) => @lem7189630 _135521 a s h2)). Qed.
Lemma lem7190606 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term126 _135521 s a y f) = (term165 _135521 s y f a).
Proof. exact (EQ_MP (@lem7190605 _135521 y f a s h1 h2) (@lem7189630 _135521 a s h2)). Qed.
Lemma lem7190607 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (@FINITE _135521 s) = ((term126 _135521 s a y f) = (term165 _135521 s y f a)).
Proof. exact (prop_ext (fun h3 : @FINITE _135521 s => @lem7190606 _135521 y f a s h1 h2) (fun h3 : (term126 _135521 s a y f) = (term165 _135521 s y f a) => @lem7189631 _135521 s h1)). Qed.
Lemma lem7190608 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : @IN _135521 a s) : (term126 _135521 s a y f) = (term165 _135521 s y f a).
Proof. exact (EQ_MP (@lem7190607 _135521 y f a s h1 h2) (@lem7189631 _135521 s h1)). Qed.
Lemma lem7190609 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : term101 _135521 a s) : (@IN _135521 a s) = ((term126 _135521 s a y f) = (term165 _135521 s y f a)).
Proof. exact (prop_ext (fun h3 : @IN _135521 a s => @lem7190608 _135521 y f a s h1 h3) (fun h3 : (term126 _135521 s a y f) = (term165 _135521 s y f a) => @lem7190603 _135521 a s h2)). Qed.
Lemma lem7190610 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : @FINITE _135521 s) (h2 : term101 _135521 a s) : (term126 _135521 s a y f) = (term165 _135521 s y f a).
Proof. exact (EQ_MP (@lem7190609 _135521 y f a s h1 h2) (@lem7190603 _135521 a s h2)). Qed.
Lemma lem7190611 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : term101 _135521 a s) : (@FINITE _135521 s) = ((term126 _135521 s a y f) = (term165 _135521 s y f a)).
Proof. exact (prop_ext (fun h2 : @FINITE _135521 s => @lem7190610 _135521 y f a s h2 h1) (fun h2 : (term126 _135521 s a y f) = (term165 _135521 s y f a) => @lem7190604 _135521 a s h1)). Qed.
Lemma lem7190612 {_135521 : Type'} (y : real) (f : _135521 -> real) (a : _135521) (s : _135521 -> Prop) (h1 : term101 _135521 a s) : (term126 _135521 s a y f) = (term165 _135521 s y f a).
Proof. exact (EQ_MP (@lem7190611 _135521 y f a s h1) (@lem7190604 _135521 a s h1)). Qed.
Lemma lem7190613 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) (a : _135521) : term326 _135521 s y f a.
Proof. exact (fun h0 : term101 _135521 a s => @lem7190612 _135521 y f a s h0). Qed.
Lemma lem7190618 {_135521 : Type'} (s : _135521 -> Prop) (y : real) (f : _135521 -> real) : term327 _135521 s y f.
Proof. exact (fun a : _135521 => @lem7190613 _135521 s y f a). Qed.
Lemma lem7190623 {_135521 : Type'} (y : real) (f : _135521 -> real) : term328 _135521 y f.
Proof. exact (fun s : _135521 -> Prop => @lem7190618 _135521 s y f). Qed.
