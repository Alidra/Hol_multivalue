Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_SUBSET_SIMPLE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import IN_DIFF_spec.
Require Import NSUM_SUBSET_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem7006899 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7006900 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7006901 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7006900 t1) (@lem7006899 t1)). Qed.
Lemma lem7006902 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7006901 t1 t2). Qed.
Lemma lem7006903 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7006904 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7006903 t1 t2) (@lem7006902 t1 t2)). Qed.
Lemma lem7006905 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7006904 t1 t2 t3). Qed.
Lemma lem7006906 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7006907 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7006906 t1 t2 t3) (@lem7006905 t1 t2 t3)). Qed.
Lemma lem7006908 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7006907 t1 t2 t3)). Qed.
Lemma lem7006909 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7006910 {A : Type'} (u : A -> Prop) (h1 : term7 A) : term8 A u.
Proof. exact (@lem7006909 A h1 u). Qed.
Lemma lem7006911 {A : Type'} (u : A -> Prop) : (term8 A u) = (term9 A u).
Proof. exact (eq_refl (term8 A u)). Qed.
Lemma lem7006912 {A : Type'} (u : A -> Prop) (h1 : term7 A) : term9 A u.
Proof. exact (EQ_MP (@lem7006911 A u) (@lem7006910 A u h1)). Qed.
Lemma lem7006913 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term7 A) : term10 A u v.
Proof. exact (@lem7006912 A u h1 v). Qed.
Lemma lem7006914 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term10 A u v) = (term11 A u v).
Proof. exact (eq_refl (term10 A u v)). Qed.
Lemma lem7006915 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term7 A) : term11 A u v.
Proof. exact (EQ_MP (@lem7006914 A u v) (@lem7006913 A u v h1)). Qed.
Lemma lem7006916 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term7 A) : term12 A u v f.
Proof. exact (@lem7006915 A u v h1 f). Qed.
Lemma lem7006917 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term12 A u v f) = (term13 A u v f).
Proof. exact (eq_refl (term12 A u v f)). Qed.
Lemma lem7006918 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term7 A) : term13 A u v f.
Proof. exact (EQ_MP (@lem7006917 A u v f) (@lem7006916 A u v f h1)). Qed.
Lemma lem7006919 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term14 A u v f) : term14 A u v f.
Proof. exact (h1). Qed.
Lemma lem7006920 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term7 A) (h2 : term14 A u v f) : term15 A u v f.
Proof. exact (@lem7006918 A u v f h1 (@lem7006919 A u v f h2)). Qed.
Lemma lem7006921 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term14 A u v f) : term16 A u v f.
Proof. exact (fun h0 : term7 A => @lem7006920 A u v f h0 h1). Qed.
Lemma lem7006922 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7006923 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term7 A) (h2 : term14 A u v f) : term15 A u v f.
Proof. exact (@lem7006921 A u v f h2 (@lem7006922 A h1)). Qed.
Lemma lem7006924 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term7 A) : term13 A u v f.
Proof. exact (fun h0 : term14 A u v f => @lem7006923 A u v f h1 h0). Qed.
Lemma lem7006925 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term7 A) : term11 A u v.
Proof. exact (fun f : A -> nat => @lem7006924 A u v f h1). Qed.
Lemma lem7006926 {A : Type'} (u : A -> Prop) (h1 : term7 A) : term9 A u.
Proof. exact (fun v : A -> Prop => @lem7006925 A u v h1). Qed.
Lemma lem7006927 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (fun u : A -> Prop => @lem7006926 A u h1). Qed.
Lemma lem7006928 {A : Type'} : term17 A.
Proof. exact (fun h0 : term7 A => @lem7006927 A h0). Qed.
Lemma lem7006929 {A : Type'} : term7 A.
Proof. exact (@lem7006928 A (@lem7006898 A)). Qed.
Lemma lem7006930 {A : Type'} (u : A -> Prop) : term8 A u.
Proof. exact (@lem7006929 A u). Qed.
Lemma lem7006931 {A : Type'} (u : A -> Prop) : (term8 A u) = (term9 A u).
Proof. exact (eq_refl (term8 A u)). Qed.
Lemma lem7006932 {A : Type'} (u : A -> Prop) : term9 A u.
Proof. exact (EQ_MP (@lem7006931 A u) (@lem7006930 A u)). Qed.
Lemma lem7006933 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term10 A u v.
Proof. exact (@lem7006932 A u v). Qed.
Lemma lem7006934 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term10 A u v) = (term11 A u v).
Proof. exact (eq_refl (term10 A u v)). Qed.
Lemma lem7006935 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term11 A u v.
Proof. exact (EQ_MP (@lem7006934 A u v) (@lem7006933 A u v)). Qed.
Lemma lem7006936 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term12 A u v f.
Proof. exact (@lem7006935 A u v f). Qed.
Lemma lem7006937 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term12 A u v f) = (term13 A u v f).
Proof. exact (eq_refl (term12 A u v f)). Qed.
Lemma lem7006939 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term18 _128971 u v) : term18 _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7006940 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7006941 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7006943 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term13 A u v f.
Proof. exact (EQ_MP (@lem7006937 A u v f) (@lem7006936 A u v f)). Qed.
Lemma lem7006944 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term13 _128971 u v f.
Proof. exact (@lem7006943 _128971 u v f). Qed.
Lemma lem7006946 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7006947 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term14 _128971 u v f) = (term20 _128971 u v f).
Proof. exact (@lem7006946 (term14 _128971 u v f)). Qed.
Lemma lem7006948 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term20 _128971 u v f) = (term14 _128971 u v f).
Proof. exact (SYM (@lem7006947 _128971 u v f)). Qed.
Lemma lem7006949 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term21 _128971 u v f) : term21 _128971 u v f.
Proof. exact (h1). Qed.
Lemma lem7006950 {_128971 : Type'} : term22 _128971.
Proof. exact (@lem3205495 _128971). Qed.
Lemma lem7006952 {_128971 : Type'} : term23 _128971.
Proof. exact (@lem3194148 _128971). Qed.
Lemma lem7006954 {_128971 : Type'} : term24 _128971.
Proof. exact (@lem3599924 _128971). Qed.
Lemma lem7006958 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term25 _128971 u v f) : term25 _128971 u v f.
Proof. exact (h1). Qed.
Lemma lem7006959 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term26 _128971 u v f.
Proof. exact (fun h0 : term25 _128971 u v f => @lem7006958 _128971 u v f h0). Qed.
Lemma lem7006960 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term26 _128971 u v f) : term26 _128971 u v f.
Proof. exact (h1). Qed.
Lemma lem7006961 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term25 _128971 u v f) : term25 _128971 u v f.
Proof. exact (h1). Qed.
Lemma lem7006962 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term25 _128971 u v f) (h2 : term26 _128971 u v f) : term25 _128971 u v f.
Proof. exact (@lem7006960 _128971 u v f h2 (@lem7006961 _128971 u v f h1)). Qed.
Lemma lem7006963 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term25 _128971 u v f) : term27 _128971 u v f.
Proof. exact (fun h0 : term26 _128971 u v f => @lem7006962 _128971 u v f h1 h0). Qed.
Lemma lem7006964 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term26 _128971 u v f) : term26 _128971 u v f.
Proof. exact (h1). Qed.
Lemma lem7006965 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term25 _128971 u v f) (h2 : term26 _128971 u v f) : term25 _128971 u v f.
Proof. exact (@lem7006963 _128971 u v f h1 (@lem7006964 _128971 u v f h2)). Qed.
Lemma lem7006966 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term26 _128971 u v f) : term26 _128971 u v f.
Proof. exact (fun h0 : term25 _128971 u v f => @lem7006965 _128971 u v f h0 h1). Qed.
Lemma lem7006967 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term28 _128971 u v f.
Proof. exact (fun h0 : term26 _128971 u v f => @lem7006966 _128971 u v f h0). Qed.
Lemma lem7006970 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term26 _128971 u v f.
Proof. exact (@lem7006967 _128971 u v f (@lem7006959 _128971 u v f)). Qed.
Lemma lem7006971 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term26 _128971 u v f.
Proof. exact (@lem7006970 _128971 u v f). Qed.
Lemma lem7007031 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7007032 {_128971 : Type'} : (term29 _128971) = (term30 _128971).
Proof. exact (@lem7007031 (term22 _128971)). Qed.
Lemma lem7007047 {_128971 : Type'} : (term31 _128971) = (term31 _128971).
Proof. exact (eq_refl (term31 _128971)). Qed.
Lemma lem7007048 {_128971 : Type'} : (term32 _128971) = (term33 _128971).
Proof. exact (MK_COMB (@lem7007047 _128971) (@lem7007032 _128971)). Qed.
Lemma lem7007051 {_128971 : Type'} : (term34 _128971) = (term34 _128971).
Proof. exact (eq_refl (term34 _128971)). Qed.
Lemma lem7007052 {_128971 : Type'} : (term35 _128971) = (term36 _128971).
Proof. exact (MK_COMB (@lem7007051 _128971) (@lem7007048 _128971)). Qed.
Lemma lem7007055 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term37 _128971 u v f) = (term37 _128971 u v f).
Proof. exact (eq_refl (term37 _128971 u v f)). Qed.
Lemma lem7007056 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term38 _128971 u v f) = (term39 _128971 u v f).
Proof. exact (MK_COMB (@lem7007055 _128971 u v f) (@lem7007052 _128971)). Qed.
Lemma lem7007059 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : (term40 _128971 u v) = (term40 _128971 u v).
Proof. exact (eq_refl (term40 _128971 u v)). Qed.
Lemma lem7007060 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term41 _128971 u v f) = (term42 _128971 u v f).
Proof. exact (MK_COMB (@lem7007059 _128971 u v) (@lem7007056 _128971 u v f)). Qed.
Lemma lem7007063 {_128971 : Type'} (v : _128971 -> Prop) : (term43 _128971 v) = (term43 _128971 v).
Proof. exact (eq_refl (term43 _128971 v)). Qed.
Lemma lem7007064 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term25 _128971 u v f) = (term44 _128971 u v f).
Proof. exact (MK_COMB (@lem7007063 _128971 v) (@lem7007060 _128971 u v f)). Qed.
Lemma lem7007067 {_128971 : Type'} (v : _128971 -> Prop) (f : _128971 -> nat) : (term45 _128971 v f) = (term46 _128971 v f).
Proof. exact (fun_ext (fun u : _128971 -> Prop => @lem7007064 _128971 u v f)). Qed.
Lemma lem7007068 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007069 {_128971 : Type'} (v : _128971 -> Prop) (f : _128971 -> nat) : (term47 _128971 v f) = (term48 _128971 v f).
Proof. exact (MK_COMB (@lem7007068 _128971) (@lem7007067 _128971 v f)). Qed.
Lemma lem7007074 {_128971 : Type'} (f : _128971 -> nat) : (term49 _128971 f) = (term50 _128971 f).
Proof. exact (fun_ext (fun v : _128971 -> Prop => @lem7007069 _128971 v f)). Qed.
Lemma lem7007075 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007076 {_128971 : Type'} (f : _128971 -> nat) : (term51 _128971 f) = (term52 _128971 f).
Proof. exact (MK_COMB (@lem7007075 _128971) (@lem7007074 _128971 f)). Qed.
Lemma lem7007081 {_128971 : Type'} : (term53 _128971) = (term54 _128971).
Proof. exact (fun_ext (fun f : _128971 -> nat => @lem7007076 _128971 f)). Qed.
Lemma lem7007082 {_128971 : Type'} : (@all (_128971 -> nat)) = (@all (_128971 -> nat)).
Proof. exact (eq_refl (@all (_128971 -> nat))). Qed.
Lemma lem7007091 {_128971 : Type'} : (term55 _128971) = (term56 _128971).
Proof. exact (MK_COMB (@lem7007082 _128971) (@lem7007081 _128971)). Qed.
Lemma lem7007102 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : ((term57 _128971 x s t) = (term58 _128971 s x t)) = ((term57 _128971 x s t) = (term58 _128971 s x t)).
Proof. exact (eq_refl ((term57 _128971 x s t) = (term58 _128971 s x t))). Qed.
Lemma lem7007103 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term59 _128971 s t) = (term59 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7007102 _128971 s x t)). Qed.
Lemma lem7007104 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7007105 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term60 _128971 s t) = (term60 _128971 s t).
Proof. exact (MK_COMB (@lem7007104 _128971) (@lem7007103 _128971 s t)). Qed.
Lemma lem7007106 {_128971 : Type'} (s : _128971 -> Prop) : (term61 _128971 s) = (term61 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007105 _128971 s t)). Qed.
Lemma lem7007107 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007108 {_128971 : Type'} (s : _128971 -> Prop) : (term62 _128971 s) = (term62 _128971 s).
Proof. exact (MK_COMB (@lem7007107 _128971) (@lem7007106 _128971 s)). Qed.
Lemma lem7007109 {_128971 : Type'} : (term63 _128971) = (term63 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007108 _128971 s)). Qed.
Lemma lem7007110 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007111 {_128971 : Type'} : (term22 _128971) = (term22 _128971).
Proof. exact (MK_COMB (@lem7007110 _128971) (@lem7007109 _128971)). Qed.
Lemma lem7007112 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7007113 {_128971 : Type'} : (term30 _128971) = (term30 _128971).
Proof. exact (MK_COMB (@lem7007112) (@lem7007111 _128971)). Qed.
Lemma lem7007118 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term64 _128971 s x t) = (term64 _128971 s x t).
Proof. exact (eq_refl (term64 _128971 s x t)). Qed.
Lemma lem7007119 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term65 _128971 s t) = (term65 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7007118 _128971 s x t)). Qed.
Lemma lem7007120 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7007121 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term66 _128971 s t) = (term66 _128971 s t).
Proof. exact (MK_COMB (@lem7007120 _128971) (@lem7007119 _128971 s t)). Qed.
Lemma lem7007124 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term67 _128971 s t) = (term67 _128971 s t).
Proof. exact (eq_refl (term67 _128971 s t)). Qed.
Lemma lem7007125 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : ((@SUBSET _128971 s t) = (term66 _128971 s t)) = ((@SUBSET _128971 s t) = (term66 _128971 s t)).
Proof. exact (MK_COMB (@lem7007124 _128971 s t) (@lem7007121 _128971 s t)). Qed.
Lemma lem7007126 {_128971 : Type'} (s : _128971 -> Prop) : (term68 _128971 s) = (term68 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007125 _128971 s t)). Qed.
Lemma lem7007127 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007128 {_128971 : Type'} (s : _128971 -> Prop) : (term69 _128971 s) = (term69 _128971 s).
Proof. exact (MK_COMB (@lem7007127 _128971) (@lem7007126 _128971 s)). Qed.
Lemma lem7007129 {_128971 : Type'} : (term70 _128971) = (term70 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007128 _128971 s)). Qed.
Lemma lem7007130 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007131 {_128971 : Type'} : (term23 _128971) = (term23 _128971).
Proof. exact (MK_COMB (@lem7007130 _128971) (@lem7007129 _128971)). Qed.
Lemma lem7007132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7007133 {_128971 : Type'} : (term31 _128971) = (term31 _128971).
Proof. exact (MK_COMB (@lem7007132) (@lem7007131 _128971)). Qed.
Lemma lem7007134 {_128971 : Type'} : (term33 _128971) = (term33 _128971).
Proof. exact (MK_COMB (@lem7007133 _128971) (@lem7007113 _128971)). Qed.
Lemma lem7007143 {_128971 : Type'} (t : _128971 -> Prop) (s : _128971 -> Prop) : (term71 _128971 t s) = (term71 _128971 t s).
Proof. exact (eq_refl (term71 _128971 t s)). Qed.
Lemma lem7007144 {_128971 : Type'} (s : _128971 -> Prop) : (term72 _128971 s) = (term72 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007143 _128971 t s)). Qed.
Lemma lem7007145 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007146 {_128971 : Type'} (s : _128971 -> Prop) : (term73 _128971 s) = (term73 _128971 s).
Proof. exact (MK_COMB (@lem7007145 _128971) (@lem7007144 _128971 s)). Qed.
Lemma lem7007147 {_128971 : Type'} : (term74 _128971) = (term74 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007146 _128971 s)). Qed.
Lemma lem7007148 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007149 {_128971 : Type'} : (term24 _128971) = (term24 _128971).
Proof. exact (MK_COMB (@lem7007148 _128971) (@lem7007147 _128971)). Qed.
Lemma lem7007150 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7007151 {_128971 : Type'} : (term34 _128971) = (term34 _128971).
Proof. exact (MK_COMB (@lem7007150) (@lem7007149 _128971)). Qed.
Lemma lem7007152 {_128971 : Type'} : (term36 _128971) = (term36 _128971).
Proof. exact (MK_COMB (@lem7007151 _128971) (@lem7007134 _128971)). Qed.
Lemma lem7007157 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term75 _128971 u v f x) = (term75 _128971 u v f x).
Proof. exact (eq_refl (term75 _128971 u v f x)). Qed.
Lemma lem7007158 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term76 _128971 u v f) = (term76 _128971 u v f).
Proof. exact (fun_ext (fun x : _128971 => @lem7007157 _128971 u v f x)). Qed.
Lemma lem7007159 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7007160 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term77 _128971 u v f) = (term77 _128971 u v f).
Proof. exact (MK_COMB (@lem7007159 _128971) (@lem7007158 _128971 u v f)). Qed.
Lemma lem7007163 {_128971 : Type'} (v : _128971 -> Prop) : (term78 _128971 v) = (term78 _128971 v).
Proof. exact (eq_refl (term78 _128971 v)). Qed.
Lemma lem7007164 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term79 _128971 u v f) = (term79 _128971 u v f).
Proof. exact (MK_COMB (@lem7007163 _128971 v) (@lem7007160 _128971 u v f)). Qed.
Lemma lem7007167 {_128971 : Type'} (u : _128971 -> Prop) : (term78 _128971 u) = (term78 _128971 u).
Proof. exact (eq_refl (term78 _128971 u)). Qed.
Lemma lem7007168 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term14 _128971 u v f) = (term14 _128971 u v f).
Proof. exact (MK_COMB (@lem7007167 _128971 u) (@lem7007164 _128971 u v f)). Qed.
Lemma lem7007169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7007170 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term21 _128971 u v f) = (term21 _128971 u v f).
Proof. exact (MK_COMB (@lem7007169) (@lem7007168 _128971 u v f)). Qed.
Lemma lem7007171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7007172 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term37 _128971 u v f) = (term37 _128971 u v f).
Proof. exact (MK_COMB (@lem7007171) (@lem7007170 _128971 u v f)). Qed.
Lemma lem7007173 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term39 _128971 u v f) = (term39 _128971 u v f).
Proof. exact (MK_COMB (@lem7007172 _128971 u v f) (@lem7007152 _128971)). Qed.
Lemma lem7007176 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : (term40 _128971 u v) = (term40 _128971 u v).
Proof. exact (eq_refl (term40 _128971 u v)). Qed.
Lemma lem7007177 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term42 _128971 u v f) = (term42 _128971 u v f).
Proof. exact (MK_COMB (@lem7007176 _128971 u v) (@lem7007173 _128971 u v f)). Qed.
Lemma lem7007180 {_128971 : Type'} (v : _128971 -> Prop) : (term43 _128971 v) = (term43 _128971 v).
Proof. exact (eq_refl (term43 _128971 v)). Qed.
Lemma lem7007181 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term44 _128971 u v f) = (term44 _128971 u v f).
Proof. exact (MK_COMB (@lem7007180 _128971 v) (@lem7007177 _128971 u v f)). Qed.
Lemma lem7007182 {_128971 : Type'} (v : _128971 -> Prop) (f : _128971 -> nat) : (term46 _128971 v f) = (term46 _128971 v f).
Proof. exact (fun_ext (fun u : _128971 -> Prop => @lem7007181 _128971 u v f)). Qed.
Lemma lem7007183 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007184 {_128971 : Type'} (v : _128971 -> Prop) (f : _128971 -> nat) : (term48 _128971 v f) = (term48 _128971 v f).
Proof. exact (MK_COMB (@lem7007183 _128971) (@lem7007182 _128971 v f)). Qed.
Lemma lem7007185 {_128971 : Type'} (f : _128971 -> nat) : (term50 _128971 f) = (term50 _128971 f).
Proof. exact (fun_ext (fun v : _128971 -> Prop => @lem7007184 _128971 v f)). Qed.
Lemma lem7007186 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007187 {_128971 : Type'} (f : _128971 -> nat) : (term52 _128971 f) = (term52 _128971 f).
Proof. exact (MK_COMB (@lem7007186 _128971) (@lem7007185 _128971 f)). Qed.
Lemma lem7007188 {_128971 : Type'} : (term54 _128971) = (term54 _128971).
Proof. exact (fun_ext (fun f : _128971 -> nat => @lem7007187 _128971 f)). Qed.
Lemma lem7007189 {_128971 : Type'} : (@all (_128971 -> nat)) = (@all (_128971 -> nat)).
Proof. exact (eq_refl (@all (_128971 -> nat))). Qed.
Lemma lem7007190 {_128971 : Type'} : (term56 _128971) = (term56 _128971).
Proof. exact (MK_COMB (@lem7007189 _128971) (@lem7007188 _128971)). Qed.
Lemma lem7007289 {_128971 : Type'} : (term55 _128971) = (term56 _128971).
Proof. exact (TRANS (@lem7007091 _128971) (@lem7007190 _128971)). Qed.
Lemma lem7007290 {_128971 : Type'} : (term56 _128971) = (term55 _128971).
Proof. exact (SYM (@lem7007289 _128971)). Qed.
Lemma lem7007293 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term21 _128971 u v f) : term21 _128971 u v f.
Proof. exact (h1). Qed.
Lemma lem7007294 {_128971 : Type'} (h1 : term24 _128971) : term24 _128971.
Proof. exact (h1). Qed.
Lemma lem7007295 {_128971 : Type'} (h1 : term23 _128971) : term23 _128971.
Proof. exact (h1). Qed.
Lemma lem7007296 {_128971 : Type'} (h1 : term22 _128971) : term22 _128971.
Proof. exact (h1). Qed.
Lemma lem7007302 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7007308 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7007317 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term80 _128971 u v f x) = (term81 _128971 u v f x).
Proof. exact (@lem17362 (term57 _128971 x u v) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7007318 {_128971 : Type'} (P : _128971 -> Prop) : (term82 _128971 P) = (term83 _128971 P).
Proof. exact (@lem18392 _128971 P). Qed.
Lemma lem7007319 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term84 _128971 u v f) = (term85 _128971 u v f).
Proof. exact (@lem7007318 _128971 (term76 _128971 u v f)). Qed.
Lemma lem7007320 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term86 _128971 u v f x) = (term75 _128971 u v f x).
Proof. exact (eq_refl (term86 _128971 u v f x)). Qed.
Lemma lem7007321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7007322 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term87 _128971 u v f x) = (term80 _128971 u v f x).
Proof. exact (MK_COMB (@lem7007321) (@lem7007320 _128971 u v f x)). Qed.
Lemma lem7007323 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term87 _128971 u v f x) = (term81 _128971 u v f x).
Proof. exact (TRANS (@lem7007322 _128971 u v f x) (@lem7007317 _128971 u v f x)). Qed.
Lemma lem7007324 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term88 _128971 u v f) = (term89 _128971 u v f).
Proof. exact (fun_ext (fun x : _128971 => @lem7007323 _128971 u v f x)). Qed.
Lemma lem7007325 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7007326 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term85 _128971 u v f) = (term90 _128971 u v f).
Proof. exact (MK_COMB (@lem7007325 _128971) (@lem7007324 _128971 u v f)). Qed.
Lemma lem7007327 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term84 _128971 u v f) = (term90 _128971 u v f).
Proof. exact (TRANS (@lem7007319 _128971 u v f) (@lem7007326 _128971 u v f)). Qed.
Lemma lem7007329 {_128971 : Type'} (v : _128971 -> Prop) : (term91 _128971 v) = (term91 _128971 v).
Proof. exact (eq_refl (term91 _128971 v)). Qed.
Lemma lem7007330 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term92 _128971 u v f) = (term93 _128971 u v f).
Proof. exact (MK_COMB (@lem7007329 _128971 v) (@lem7007327 _128971 u v f)). Qed.
Lemma lem7007331 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term94 _128971 u v f) = (term92 _128971 u v f).
Proof. exact (@lem17045 (@FINITE _128971 v) (term77 _128971 u v f)). Qed.
Lemma lem7007332 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term94 _128971 u v f) = (term93 _128971 u v f).
Proof. exact (TRANS (@lem7007331 _128971 u v f) (@lem7007330 _128971 u v f)). Qed.
Lemma lem7007334 {_128971 : Type'} (u : _128971 -> Prop) : (term91 _128971 u) = (term91 _128971 u).
Proof. exact (eq_refl (term91 _128971 u)). Qed.
Lemma lem7007335 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term95 _128971 u v f) = (term96 _128971 u v f).
Proof. exact (MK_COMB (@lem7007334 _128971 u) (@lem7007332 _128971 u v f)). Qed.
Lemma lem7007336 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term21 _128971 u v f) = (term95 _128971 u v f).
Proof. exact (@lem17045 (@FINITE _128971 u) (term79 _128971 u v f)). Qed.
Lemma lem7007337 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term21 _128971 u v f) = (term96 _128971 u v f).
Proof. exact (TRANS (@lem7007336 _128971 u v f) (@lem7007335 _128971 u v f)). Qed.
Lemma lem7007388 {A : Type'} (P : Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7007389 {_128971 : Type'} (P : Prop) (Q : _128971 -> Prop) : (term97 _128971 P Q) = (term98 _128971 P Q).
Proof. exact (@lem7007388 _128971 P Q). Qed.
Lemma lem7007390 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term99 _128971 u v f) = (term100 _128971 u v f).
Proof. exact (@lem7007389 _128971 (term101 _128971 v) (term89 _128971 u v f)). Qed.
Lemma lem7007391 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term102 _128971 u v f x) = (term81 _128971 u v f x).
Proof. exact (eq_refl (term102 _128971 u v f x)). Qed.
Lemma lem7007392 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term103 _128971 u v f) = (term89 _128971 u v f).
Proof. exact (fun_ext (fun x : _128971 => @lem7007391 _128971 u v f x)). Qed.
Lemma lem7007393 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7007394 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term104 _128971 u v f) = (term90 _128971 u v f).
Proof. exact (MK_COMB (@lem7007393 _128971) (@lem7007392 _128971 u v f)). Qed.
Lemma lem7007395 {_128971 : Type'} (v : _128971 -> Prop) : (term91 _128971 v) = (term91 _128971 v).
Proof. exact (eq_refl (term91 _128971 v)). Qed.
Lemma lem7007396 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term99 _128971 u v f) = (term93 _128971 u v f).
Proof. exact (MK_COMB (@lem7007395 _128971 v) (@lem7007394 _128971 u v f)). Qed.
Lemma lem7007397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7007398 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term105 _128971 u v f) = (term106 _128971 u v f).
Proof. exact (MK_COMB (@lem7007397) (@lem7007396 _128971 u v f)). Qed.
Lemma lem7007399 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term102 _128971 u v f x) = (term81 _128971 u v f x).
Proof. exact (eq_refl (term102 _128971 u v f x)). Qed.
Lemma lem7007400 {_128971 : Type'} (v : _128971 -> Prop) : (term91 _128971 v) = (term91 _128971 v).
Proof. exact (eq_refl (term91 _128971 v)). Qed.
Lemma lem7007401 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term107 _128971 u v f x) = (term108 _128971 u v f x).
Proof. exact (MK_COMB (@lem7007400 _128971 v) (@lem7007399 _128971 u v f x)). Qed.
Lemma lem7007402 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term109 _128971 u v f) = (term110 _128971 u v f).
Proof. exact (fun_ext (fun x : _128971 => @lem7007401 _128971 u v f x)). Qed.
Lemma lem7007403 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7007404 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term100 _128971 u v f) = (term111 _128971 u v f).
Proof. exact (MK_COMB (@lem7007403 _128971) (@lem7007402 _128971 u v f)). Qed.
Lemma lem7007405 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : ((term99 _128971 u v f) = (term100 _128971 u v f)) = ((term93 _128971 u v f) = (term111 _128971 u v f)).
Proof. exact (MK_COMB (@lem7007398 _128971 u v f) (@lem7007404 _128971 u v f)). Qed.
Lemma lem7007406 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term93 _128971 u v f) = (term111 _128971 u v f).
Proof. exact (EQ_MP (@lem7007405 _128971 u v f) (@lem7007390 _128971 u v f)). Qed.
Lemma lem7007407 {_128971 : Type'} (u : _128971 -> Prop) : (term91 _128971 u) = (term91 _128971 u).
Proof. exact (eq_refl (term91 _128971 u)). Qed.
Lemma lem7007408 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term96 _128971 u v f) = (term112 _128971 u v f).
Proof. exact (MK_COMB (@lem7007407 _128971 u) (@lem7007406 _128971 u v f)). Qed.
Lemma lem7007410 {A : Type'} (P : Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7007411 {_128971 : Type'} (P : Prop) (Q : _128971 -> Prop) : (term97 _128971 P Q) = (term98 _128971 P Q).
Proof. exact (@lem7007410 _128971 P Q). Qed.
Lemma lem7007412 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term113 _128971 u v f) = (term114 _128971 u v f).
Proof. exact (@lem7007411 _128971 (term101 _128971 u) (term110 _128971 u v f)). Qed.
Lemma lem7007413 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term115 _128971 u v f x) = (term108 _128971 u v f x).
Proof. exact (eq_refl (term115 _128971 u v f x)). Qed.
Lemma lem7007414 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term116 _128971 u v f) = (term110 _128971 u v f).
Proof. exact (fun_ext (fun x : _128971 => @lem7007413 _128971 u v f x)). Qed.
Lemma lem7007415 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7007416 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term117 _128971 u v f) = (term111 _128971 u v f).
Proof. exact (MK_COMB (@lem7007415 _128971) (@lem7007414 _128971 u v f)). Qed.
Lemma lem7007417 {_128971 : Type'} (u : _128971 -> Prop) : (term91 _128971 u) = (term91 _128971 u).
Proof. exact (eq_refl (term91 _128971 u)). Qed.
Lemma lem7007418 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term113 _128971 u v f) = (term112 _128971 u v f).
Proof. exact (MK_COMB (@lem7007417 _128971 u) (@lem7007416 _128971 u v f)). Qed.
Lemma lem7007419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7007420 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term118 _128971 u v f) = (term119 _128971 u v f).
Proof. exact (MK_COMB (@lem7007419) (@lem7007418 _128971 u v f)). Qed.
Lemma lem7007421 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term115 _128971 u v f x) = (term108 _128971 u v f x).
Proof. exact (eq_refl (term115 _128971 u v f x)). Qed.
Lemma lem7007422 {_128971 : Type'} (u : _128971 -> Prop) : (term91 _128971 u) = (term91 _128971 u).
Proof. exact (eq_refl (term91 _128971 u)). Qed.
Lemma lem7007423 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x : _128971) : (term120 _128971 u v f x) = (term121 _128971 u v f x).
Proof. exact (MK_COMB (@lem7007422 _128971 u) (@lem7007421 _128971 u v f x)). Qed.
Lemma lem7007424 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term122 _128971 u v f) = (term123 _128971 u v f).
Proof. exact (fun_ext (fun x : _128971 => @lem7007423 _128971 u v f x)). Qed.
Lemma lem7007425 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7007426 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term114 _128971 u v f) = (term124 _128971 u v f).
Proof. exact (MK_COMB (@lem7007425 _128971) (@lem7007424 _128971 u v f)). Qed.
Lemma lem7007427 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : ((term113 _128971 u v f) = (term114 _128971 u v f)) = ((term112 _128971 u v f) = (term124 _128971 u v f)).
Proof. exact (MK_COMB (@lem7007420 _128971 u v f) (@lem7007426 _128971 u v f)). Qed.
Lemma lem7007428 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term112 _128971 u v f) = (term124 _128971 u v f).
Proof. exact (EQ_MP (@lem7007427 _128971 u v f) (@lem7007412 _128971 u v f)). Qed.
Lemma lem7007430 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term96 _128971 u v f) = (term124 _128971 u v f).
Proof. exact (TRANS (@lem7007408 _128971 u v f) (@lem7007428 _128971 u v f)). Qed.
Lemma lem7007431 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term21 _128971 u v f) = (term124 _128971 u v f).
Proof. exact (TRANS (@lem7007337 _128971 u v f) (@lem7007430 _128971 u v f)). Qed.
Lemma lem7007432 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term21 _128971 u v f) : term124 _128971 u v f.
Proof. exact (EQ_MP (@lem7007431 _128971 u v f) (@lem7007293 _128971 u v f h1)). Qed.
Lemma lem7007439 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term125 _128971 s t) = (term126 _128971 s t).
Proof. exact (@lem17045 (@FINITE _128971 t) (@SUBSET _128971 s t)). Qed.
Lemma lem7007440 {_128971 : Type'} (s : _128971 -> Prop) : (@FINITE _128971 s) = (@FINITE _128971 s).
Proof. exact (eq_refl (@FINITE _128971 s)). Qed.
Lemma lem7007441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7007442 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term127 _128971 s t) = (term128 _128971 s t).
Proof. exact (MK_COMB (@lem7007441) (@lem7007439 _128971 s t)). Qed.
Lemma lem7007443 {_128971 : Type'} (t : _128971 -> Prop) (s : _128971 -> Prop) : (term129 _128971 t s) = (term130 _128971 t s).
Proof. exact (MK_COMB (@lem7007442 _128971 s t) (@lem7007440 _128971 s)). Qed.
Lemma lem7007444 {_128971 : Type'} (t : _128971 -> Prop) (s : _128971 -> Prop) : (term71 _128971 t s) = (term129 _128971 t s).
Proof. exact (@lem17265 (term18 _128971 s t) (@FINITE _128971 s)). Qed.
Lemma lem7007445 {_128971 : Type'} (t : _128971 -> Prop) (s : _128971 -> Prop) : (term71 _128971 t s) = (term130 _128971 t s).
Proof. exact (TRANS (@lem7007444 _128971 t s) (@lem7007443 _128971 t s)). Qed.
Lemma lem7007446 {_128971 : Type'} (s : _128971 -> Prop) : (term72 _128971 s) = (term131 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007445 _128971 t s)). Qed.
Lemma lem7007447 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007448 {_128971 : Type'} (s : _128971 -> Prop) : (term73 _128971 s) = (term132 _128971 s).
Proof. exact (MK_COMB (@lem7007447 _128971) (@lem7007446 _128971 s)). Qed.
Lemma lem7007449 {_128971 : Type'} : (term74 _128971) = (term133 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007448 _128971 s)). Qed.
Lemma lem7007450 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007451 {_128971 : Type'} : (term24 _128971) = (term134 _128971).
Proof. exact (MK_COMB (@lem7007450 _128971) (@lem7007449 _128971)). Qed.
Lemma lem7007477 {A : Type'} (P : A -> Prop) (Q : Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem7007478 {_128971 : Type'} (P : type686 _128971) (Q : Prop) : (term137 _128971 P Q) = (term138 _128971 P Q).
Proof. exact (@lem7007477 (_128971 -> Prop) P Q). Qed.
Lemma lem7007479 {_128971 : Type'} (s : _128971 -> Prop) : (term139 _128971 s) = (term140 _128971 s).
Proof. exact (@lem7007478 _128971 (term141 _128971 s) (@FINITE _128971 s)). Qed.
Lemma lem7007480 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term142 _128971 s t) = (term126 _128971 s t).
Proof. exact (eq_refl (term142 _128971 s t)). Qed.
Lemma lem7007481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7007482 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term143 _128971 s t) = (term128 _128971 s t).
Proof. exact (MK_COMB (@lem7007481) (@lem7007480 _128971 s t)). Qed.
Lemma lem7007483 {_128971 : Type'} (s : _128971 -> Prop) : (@FINITE _128971 s) = (@FINITE _128971 s).
Proof. exact (eq_refl (@FINITE _128971 s)). Qed.
Lemma lem7007484 {_128971 : Type'} (t : _128971 -> Prop) (s : _128971 -> Prop) : (term144 _128971 t s) = (term130 _128971 t s).
Proof. exact (MK_COMB (@lem7007482 _128971 s t) (@lem7007483 _128971 s)). Qed.
Lemma lem7007485 {_128971 : Type'} (s : _128971 -> Prop) : (term145 _128971 s) = (term131 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007484 _128971 t s)). Qed.
Lemma lem7007486 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007487 {_128971 : Type'} (s : _128971 -> Prop) : (term139 _128971 s) = (term132 _128971 s).
Proof. exact (MK_COMB (@lem7007486 _128971) (@lem7007485 _128971 s)). Qed.
Lemma lem7007488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7007489 {_128971 : Type'} (s : _128971 -> Prop) : (term146 _128971 s) = (term147 _128971 s).
Proof. exact (MK_COMB (@lem7007488) (@lem7007487 _128971 s)). Qed.
Lemma lem7007490 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term142 _128971 s t) = (term126 _128971 s t).
Proof. exact (eq_refl (term142 _128971 s t)). Qed.
Lemma lem7007491 {_128971 : Type'} (s : _128971 -> Prop) : (term148 _128971 s) = (term141 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007490 _128971 s t)). Qed.
Lemma lem7007492 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007493 {_128971 : Type'} (s : _128971 -> Prop) : (term149 _128971 s) = (term150 _128971 s).
Proof. exact (MK_COMB (@lem7007492 _128971) (@lem7007491 _128971 s)). Qed.
Lemma lem7007494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7007495 {_128971 : Type'} (s : _128971 -> Prop) : (term151 _128971 s) = (term152 _128971 s).
Proof. exact (MK_COMB (@lem7007494) (@lem7007493 _128971 s)). Qed.
Lemma lem7007496 {_128971 : Type'} (s : _128971 -> Prop) : (@FINITE _128971 s) = (@FINITE _128971 s).
Proof. exact (eq_refl (@FINITE _128971 s)). Qed.
Lemma lem7007497 {_128971 : Type'} (s : _128971 -> Prop) : (term140 _128971 s) = (term153 _128971 s).
Proof. exact (MK_COMB (@lem7007495 _128971 s) (@lem7007496 _128971 s)). Qed.
Lemma lem7007498 {_128971 : Type'} (s : _128971 -> Prop) : ((term139 _128971 s) = (term140 _128971 s)) = ((term132 _128971 s) = (term153 _128971 s)).
Proof. exact (MK_COMB (@lem7007489 _128971 s) (@lem7007497 _128971 s)). Qed.
Lemma lem7007499 {_128971 : Type'} (s : _128971 -> Prop) : (term132 _128971 s) = (term153 _128971 s).
Proof. exact (EQ_MP (@lem7007498 _128971 s) (@lem7007479 _128971 s)). Qed.
Lemma lem7007548 {_128971 : Type'} : (term133 _128971) = (term154 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007499 _128971 s)). Qed.
Lemma lem7007549 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007584 {_128971 : Type'} : (term134 _128971) = (term155 _128971).
Proof. exact (MK_COMB (@lem7007549 _128971) (@lem7007548 _128971)). Qed.
Lemma lem7007585 {_128971 : Type'} : (term24 _128971) = (term155 _128971).
Proof. exact (TRANS (@lem7007451 _128971) (@lem7007584 _128971)). Qed.
Lemma lem7007586 {_128971 : Type'} (h1 : term24 _128971) : term155 _128971.
Proof. exact (EQ_MP (@lem7007585 _128971) (@lem7007294 _128971 h1)). Qed.
Lemma lem7007597 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term156 _128971 s x t) = (term58 _128971 s x t).
Proof. exact (@lem17362 (@IN _128971 x s) (@IN _128971 x t)). Qed.
Lemma lem7007602 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term64 _128971 s x t) = (term157 _128971 s x t).
Proof. exact (@lem17265 (@IN _128971 x s) (@IN _128971 x t)). Qed.
Lemma lem7007603 {_128971 : Type'} (P : _128971 -> Prop) : (term82 _128971 P) = (term83 _128971 P).
Proof. exact (@lem18392 _128971 P). Qed.
Lemma lem7007604 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term158 _128971 s t) = (term159 _128971 s t).
Proof. exact (@lem7007603 _128971 (term65 _128971 s t)). Qed.
Lemma lem7007605 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term160 _128971 s t x) = (term64 _128971 s x t).
Proof. exact (eq_refl (term160 _128971 s t x)). Qed.
Lemma lem7007606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7007607 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term161 _128971 s t x) = (term156 _128971 s x t).
Proof. exact (MK_COMB (@lem7007606) (@lem7007605 _128971 s x t)). Qed.
Lemma lem7007608 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term161 _128971 s t x) = (term58 _128971 s x t).
Proof. exact (TRANS (@lem7007607 _128971 s x t) (@lem7007597 _128971 s x t)). Qed.
Lemma lem7007609 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term162 _128971 s t) = (term163 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7007608 _128971 s x t)). Qed.
Lemma lem7007610 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7007611 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term159 _128971 s t) = (term164 _128971 s t).
Proof. exact (MK_COMB (@lem7007610 _128971) (@lem7007609 _128971 s t)). Qed.
Lemma lem7007612 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term158 _128971 s t) = (term164 _128971 s t).
Proof. exact (TRANS (@lem7007604 _128971 s t) (@lem7007611 _128971 s t)). Qed.
Lemma lem7007613 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term65 _128971 s t) = (term165 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7007602 _128971 s x t)). Qed.
Lemma lem7007614 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7007615 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term66 _128971 s t) = (term166 _128971 s t).
Proof. exact (MK_COMB (@lem7007614 _128971) (@lem7007613 _128971 s t)). Qed.
Lemma lem7007617 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term167 _128971 s t) = (term167 _128971 s t).
Proof. exact (eq_refl (term167 _128971 s t)). Qed.
Lemma lem7007618 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term168 _128971 s t) = (term169 _128971 s t).
Proof. exact (MK_COMB (@lem7007617 _128971 s t) (@lem7007615 _128971 s t)). Qed.
Lemma lem7007620 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term170 _128971 s t) = (term170 _128971 s t).
Proof. exact (eq_refl (term170 _128971 s t)). Qed.
Lemma lem7007621 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term171 _128971 s t) = (term172 _128971 s t).
Proof. exact (MK_COMB (@lem7007620 _128971 s t) (@lem7007612 _128971 s t)). Qed.
Lemma lem7007622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7007623 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term173 _128971 s t) = (term174 _128971 s t).
Proof. exact (MK_COMB (@lem7007622) (@lem7007621 _128971 s t)). Qed.
Lemma lem7007624 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term175 _128971 s t) = (term176 _128971 s t).
Proof. exact (MK_COMB (@lem7007623 _128971 s t) (@lem7007618 _128971 s t)). Qed.
Lemma lem7007625 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : ((@SUBSET _128971 s t) = (term66 _128971 s t)) = (term175 _128971 s t).
Proof. exact (@lem17784 (@SUBSET _128971 s t) (term66 _128971 s t)). Qed.
Lemma lem7007626 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : ((@SUBSET _128971 s t) = (term66 _128971 s t)) = (term176 _128971 s t).
Proof. exact (TRANS (@lem7007625 _128971 s t) (@lem7007624 _128971 s t)). Qed.
Lemma lem7007627 {_128971 : Type'} (s : _128971 -> Prop) : (term68 _128971 s) = (term177 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007626 _128971 s t)). Qed.
Lemma lem7007628 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007629 {_128971 : Type'} (s : _128971 -> Prop) : (term69 _128971 s) = (term178 _128971 s).
Proof. exact (MK_COMB (@lem7007628 _128971) (@lem7007627 _128971 s)). Qed.
Lemma lem7007630 {_128971 : Type'} : (term70 _128971) = (term179 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007629 _128971 s)). Qed.
Lemma lem7007631 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007632 {_128971 : Type'} : (term23 _128971) = (term180 _128971).
Proof. exact (MK_COMB (@lem7007631 _128971) (@lem7007630 _128971)). Qed.
Lemma lem7007638 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7007639 {_128971 : Type'} (P : type686 _128971) (Q : type686 _128971) : (term183 _128971 P Q) = (term184 _128971 P Q).
Proof. exact (@lem7007638 (_128971 -> Prop) P Q). Qed.
Lemma lem7007640 {_128971 : Type'} (s : _128971 -> Prop) : (term185 _128971 s) = (term186 _128971 s).
Proof. exact (@lem7007639 _128971 (term187 _128971 s) (term188 _128971 s)). Qed.
Lemma lem7007641 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term189 _128971 s t) = (term172 _128971 s t).
Proof. exact (eq_refl (term189 _128971 s t)). Qed.
Lemma lem7007642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7007643 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term190 _128971 s t) = (term174 _128971 s t).
Proof. exact (MK_COMB (@lem7007642) (@lem7007641 _128971 s t)). Qed.
Lemma lem7007644 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term191 _128971 s t) = (term169 _128971 s t).
Proof. exact (eq_refl (term191 _128971 s t)). Qed.
Lemma lem7007645 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term192 _128971 s t) = (term176 _128971 s t).
Proof. exact (MK_COMB (@lem7007643 _128971 s t) (@lem7007644 _128971 s t)). Qed.
Lemma lem7007646 {_128971 : Type'} (s : _128971 -> Prop) : (term193 _128971 s) = (term177 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007645 _128971 s t)). Qed.
Lemma lem7007647 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007648 {_128971 : Type'} (s : _128971 -> Prop) : (term185 _128971 s) = (term178 _128971 s).
Proof. exact (MK_COMB (@lem7007647 _128971) (@lem7007646 _128971 s)). Qed.
Lemma lem7007649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7007650 {_128971 : Type'} (s : _128971 -> Prop) : (term194 _128971 s) = (term195 _128971 s).
Proof. exact (MK_COMB (@lem7007649) (@lem7007648 _128971 s)). Qed.
Lemma lem7007651 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term189 _128971 s t) = (term172 _128971 s t).
Proof. exact (eq_refl (term189 _128971 s t)). Qed.
Lemma lem7007652 {_128971 : Type'} (s : _128971 -> Prop) : (term196 _128971 s) = (term187 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007651 _128971 s t)). Qed.
Lemma lem7007653 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007654 {_128971 : Type'} (s : _128971 -> Prop) : (term197 _128971 s) = (term198 _128971 s).
Proof. exact (MK_COMB (@lem7007653 _128971) (@lem7007652 _128971 s)). Qed.
Lemma lem7007655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7007656 {_128971 : Type'} (s : _128971 -> Prop) : (term199 _128971 s) = (term200 _128971 s).
Proof. exact (MK_COMB (@lem7007655) (@lem7007654 _128971 s)). Qed.
Lemma lem7007657 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term191 _128971 s t) = (term169 _128971 s t).
Proof. exact (eq_refl (term191 _128971 s t)). Qed.
Lemma lem7007658 {_128971 : Type'} (s : _128971 -> Prop) : (term201 _128971 s) = (term188 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7007657 _128971 s t)). Qed.
Lemma lem7007659 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007660 {_128971 : Type'} (s : _128971 -> Prop) : (term202 _128971 s) = (term203 _128971 s).
Proof. exact (MK_COMB (@lem7007659 _128971) (@lem7007658 _128971 s)). Qed.
Lemma lem7007661 {_128971 : Type'} (s : _128971 -> Prop) : (term186 _128971 s) = (term204 _128971 s).
Proof. exact (MK_COMB (@lem7007656 _128971 s) (@lem7007660 _128971 s)). Qed.
Lemma lem7007662 {_128971 : Type'} (s : _128971 -> Prop) : ((term185 _128971 s) = (term186 _128971 s)) = ((term178 _128971 s) = (term204 _128971 s)).
Proof. exact (MK_COMB (@lem7007650 _128971 s) (@lem7007661 _128971 s)). Qed.
Lemma lem7007663 {_128971 : Type'} (s : _128971 -> Prop) : (term178 _128971 s) = (term204 _128971 s).
Proof. exact (EQ_MP (@lem7007662 _128971 s) (@lem7007640 _128971 s)). Qed.
Lemma lem7007856 {_128971 : Type'} : (term179 _128971) = (term205 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007663 _128971 s)). Qed.
Lemma lem7007857 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007858 {_128971 : Type'} : (term180 _128971) = (term206 _128971).
Proof. exact (MK_COMB (@lem7007857 _128971) (@lem7007856 _128971)). Qed.
Lemma lem7007860 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7007861 {_128971 : Type'} (P : type686 _128971) (Q : type686 _128971) : (term183 _128971 P Q) = (term184 _128971 P Q).
Proof. exact (@lem7007860 (_128971 -> Prop) P Q). Qed.
Lemma lem7007862 {_128971 : Type'} : (term207 _128971) = (term208 _128971).
Proof. exact (@lem7007861 _128971 (term209 _128971) (term210 _128971)). Qed.
Lemma lem7007863 {_128971 : Type'} (s : _128971 -> Prop) : (term211 _128971 s) = (term198 _128971 s).
Proof. exact (eq_refl (term211 _128971 s)). Qed.
Lemma lem7007864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7007865 {_128971 : Type'} (s : _128971 -> Prop) : (term212 _128971 s) = (term200 _128971 s).
Proof. exact (MK_COMB (@lem7007864) (@lem7007863 _128971 s)). Qed.
Lemma lem7007866 {_128971 : Type'} (s : _128971 -> Prop) : (term213 _128971 s) = (term203 _128971 s).
Proof. exact (eq_refl (term213 _128971 s)). Qed.
Lemma lem7007867 {_128971 : Type'} (s : _128971 -> Prop) : (term214 _128971 s) = (term204 _128971 s).
Proof. exact (MK_COMB (@lem7007865 _128971 s) (@lem7007866 _128971 s)). Qed.
Lemma lem7007868 {_128971 : Type'} : (term215 _128971) = (term205 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007867 _128971 s)). Qed.
Lemma lem7007869 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007870 {_128971 : Type'} : (term207 _128971) = (term206 _128971).
Proof. exact (MK_COMB (@lem7007869 _128971) (@lem7007868 _128971)). Qed.
Lemma lem7007871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7007872 {_128971 : Type'} : (term216 _128971) = (term217 _128971).
Proof. exact (MK_COMB (@lem7007871) (@lem7007870 _128971)). Qed.
Lemma lem7007873 {_128971 : Type'} (s : _128971 -> Prop) : (term211 _128971 s) = (term198 _128971 s).
Proof. exact (eq_refl (term211 _128971 s)). Qed.
Lemma lem7007874 {_128971 : Type'} : (term218 _128971) = (term209 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007873 _128971 s)). Qed.
Lemma lem7007875 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007876 {_128971 : Type'} : (term219 _128971) = (term220 _128971).
Proof. exact (MK_COMB (@lem7007875 _128971) (@lem7007874 _128971)). Qed.
Lemma lem7007877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7007878 {_128971 : Type'} : (term221 _128971) = (term222 _128971).
Proof. exact (MK_COMB (@lem7007877) (@lem7007876 _128971)). Qed.
Lemma lem7007879 {_128971 : Type'} (s : _128971 -> Prop) : (term213 _128971 s) = (term203 _128971 s).
Proof. exact (eq_refl (term213 _128971 s)). Qed.
Lemma lem7007880 {_128971 : Type'} : (term223 _128971) = (term210 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7007879 _128971 s)). Qed.
Lemma lem7007881 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7007882 {_128971 : Type'} : (term224 _128971) = (term225 _128971).
Proof. exact (MK_COMB (@lem7007881 _128971) (@lem7007880 _128971)). Qed.
Lemma lem7007883 {_128971 : Type'} : (term208 _128971) = (term226 _128971).
Proof. exact (MK_COMB (@lem7007878 _128971) (@lem7007882 _128971)). Qed.
Lemma lem7007884 {_128971 : Type'} : ((term207 _128971) = (term208 _128971)) = ((term206 _128971) = (term226 _128971)).
Proof. exact (MK_COMB (@lem7007872 _128971) (@lem7007883 _128971)). Qed.
Lemma lem7007885 {_128971 : Type'} : (term206 _128971) = (term226 _128971).
Proof. exact (EQ_MP (@lem7007884 _128971) (@lem7007862 _128971)). Qed.
Lemma lem7008086 {_128971 : Type'} : (term180 _128971) = (term226 _128971).
Proof. exact (TRANS (@lem7007858 _128971) (@lem7007885 _128971)). Qed.
Lemma lem7008088 {A : Type'} (P : Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7008089 {_128971 : Type'} (P : Prop) (Q : _128971 -> Prop) : (term97 _128971 P Q) = (term98 _128971 P Q).
Proof. exact (@lem7008088 _128971 P Q). Qed.
Lemma lem7008090 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term227 _128971 s t) = (term228 _128971 s t).
Proof. exact (@lem7008089 _128971 (@SUBSET _128971 s t) (term163 _128971 s t)). Qed.
Lemma lem7008091 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term229 _128971 s t x) = (term58 _128971 s x t).
Proof. exact (eq_refl (term229 _128971 s t x)). Qed.
Lemma lem7008092 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term230 _128971 s t) = (term163 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008091 _128971 s x t)). Qed.
Lemma lem7008093 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7008094 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term231 _128971 s t) = (term164 _128971 s t).
Proof. exact (MK_COMB (@lem7008093 _128971) (@lem7008092 _128971 s t)). Qed.
Lemma lem7008095 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term170 _128971 s t) = (term170 _128971 s t).
Proof. exact (eq_refl (term170 _128971 s t)). Qed.
Lemma lem7008096 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term227 _128971 s t) = (term172 _128971 s t).
Proof. exact (MK_COMB (@lem7008095 _128971 s t) (@lem7008094 _128971 s t)). Qed.
Lemma lem7008097 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7008098 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term232 _128971 s t) = (term233 _128971 s t).
Proof. exact (MK_COMB (@lem7008097) (@lem7008096 _128971 s t)). Qed.
Lemma lem7008099 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term229 _128971 s t x) = (term58 _128971 s x t).
Proof. exact (eq_refl (term229 _128971 s t x)). Qed.
Lemma lem7008100 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term170 _128971 s t) = (term170 _128971 s t).
Proof. exact (eq_refl (term170 _128971 s t)). Qed.
Lemma lem7008101 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term234 _128971 s t x) = (term235 _128971 s x t).
Proof. exact (MK_COMB (@lem7008100 _128971 s t) (@lem7008099 _128971 s x t)). Qed.
Lemma lem7008102 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term236 _128971 s t) = (term237 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008101 _128971 s x t)). Qed.
Lemma lem7008103 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7008104 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term228 _128971 s t) = (term238 _128971 s t).
Proof. exact (MK_COMB (@lem7008103 _128971) (@lem7008102 _128971 s t)). Qed.
Lemma lem7008105 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : ((term227 _128971 s t) = (term228 _128971 s t)) = ((term172 _128971 s t) = (term238 _128971 s t)).
Proof. exact (MK_COMB (@lem7008098 _128971 s t) (@lem7008104 _128971 s t)). Qed.
Lemma lem7008106 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term172 _128971 s t) = (term238 _128971 s t).
Proof. exact (EQ_MP (@lem7008105 _128971 s t) (@lem7008090 _128971 s t)). Qed.
Lemma lem7008107 {_128971 : Type'} (s : _128971 -> Prop) : (term187 _128971 s) = (term239 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008106 _128971 s t)). Qed.
Lemma lem7008108 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008109 {_128971 : Type'} (s : _128971 -> Prop) : (term198 _128971 s) = (term240 _128971 s).
Proof. exact (MK_COMB (@lem7008108 _128971) (@lem7008107 _128971 s)). Qed.
Lemma lem7008111 {A B : Type'} (P : type1413 A B) : (term241 A B P) = (term242 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7008112 {_128971 : Type'} (P : type672 _128971) : (term243 _128971 P) = (term244 _128971 P).
Proof. exact (@lem7008111 (_128971 -> Prop) _128971 P). Qed.
Lemma lem7008113 {_128971 : Type'} (s : _128971 -> Prop) : (term245 _128971 s) = (term246 _128971 s).
Proof. exact (@lem7008112 _128971 (term247 _128971 s)). Qed.
Lemma lem7008114 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term248 _128971 s t) = (term237 _128971 s t).
Proof. exact (eq_refl (term248 _128971 s t)). Qed.
Lemma lem7008115 {_128971 : Type'} (x : _128971) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7008116 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) (x : _128971) : (term249 _128971 s t x) = (term250 _128971 s t x).
Proof. exact (MK_COMB (@lem7008114 _128971 s t) (@lem7008115 _128971 x)). Qed.
Lemma lem7008117 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term250 _128971 s t x) = (term235 _128971 s x t).
Proof. exact (eq_refl (term250 _128971 s t x)). Qed.
Lemma lem7008118 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term249 _128971 s t x) = (term235 _128971 s x t).
Proof. exact (TRANS (@lem7008116 _128971 s t x) (@lem7008117 _128971 s x t)). Qed.
Lemma lem7008119 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term251 _128971 s t) = (term237 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008118 _128971 s x t)). Qed.
Lemma lem7008120 {_128971 : Type'} : (@ex _128971) = (@ex _128971).
Proof. exact (eq_refl (@ex _128971)). Qed.
Lemma lem7008121 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term252 _128971 s t) = (term238 _128971 s t).
Proof. exact (MK_COMB (@lem7008120 _128971) (@lem7008119 _128971 s t)). Qed.
Lemma lem7008122 {_128971 : Type'} (s : _128971 -> Prop) : (term253 _128971 s) = (term239 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008121 _128971 s t)). Qed.
Lemma lem7008123 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008124 {_128971 : Type'} (s : _128971 -> Prop) : (term245 _128971 s) = (term240 _128971 s).
Proof. exact (MK_COMB (@lem7008123 _128971) (@lem7008122 _128971 s)). Qed.
Lemma lem7008125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7008126 {_128971 : Type'} (s : _128971 -> Prop) : (term254 _128971 s) = (term255 _128971 s).
Proof. exact (MK_COMB (@lem7008125) (@lem7008124 _128971 s)). Qed.
Lemma lem7008127 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term248 _128971 s t) = (term237 _128971 s t).
Proof. exact (eq_refl (term248 _128971 s t)). Qed.
Lemma lem7008128 {_128971 : Type'} (x : type684 _128971) (t : _128971 -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem7008129 {_128971 : Type'} (s : _128971 -> Prop) (x : type684 _128971) (t : _128971 -> Prop) : (term256 _128971 s x t) = (term257 _128971 s x t).
Proof. exact (MK_COMB (@lem7008127 _128971 s t) (@lem7008128 _128971 x t)). Qed.
Lemma lem7008130 {_128971 : Type'} (s : _128971 -> Prop) (x : type684 _128971) (t : _128971 -> Prop) : (term257 _128971 s x t) = (term258 _128971 s x t).
Proof. exact (eq_refl (term257 _128971 s x t)). Qed.
Lemma lem7008131 {_128971 : Type'} (s : _128971 -> Prop) (x : type684 _128971) (t : _128971 -> Prop) : (term256 _128971 s x t) = (term258 _128971 s x t).
Proof. exact (TRANS (@lem7008129 _128971 s x t) (@lem7008130 _128971 s x t)). Qed.
Lemma lem7008132 {_128971 : Type'} (s : _128971 -> Prop) (x : type684 _128971) : (term259 _128971 s x) = (term260 _128971 s x).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008131 _128971 s x t)). Qed.
Lemma lem7008133 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008134 {_128971 : Type'} (s : _128971 -> Prop) (x : type684 _128971) : (term261 _128971 s x) = (term262 _128971 s x).
Proof. exact (MK_COMB (@lem7008133 _128971) (@lem7008132 _128971 s x)). Qed.
Lemma lem7008135 {_128971 : Type'} (s : _128971 -> Prop) : (term263 _128971 s) = (term264 _128971 s).
Proof. exact (fun_ext (fun x : type684 _128971 => @lem7008134 _128971 s x)). Qed.
Lemma lem7008136 {_128971 : Type'} : (@ex ((_128971 -> Prop) -> _128971)) = (@ex ((_128971 -> Prop) -> _128971)).
Proof. exact (eq_refl (@ex ((_128971 -> Prop) -> _128971))). Qed.
Lemma lem7008137 {_128971 : Type'} (s : _128971 -> Prop) : (term246 _128971 s) = (term265 _128971 s).
Proof. exact (MK_COMB (@lem7008136 _128971) (@lem7008135 _128971 s)). Qed.
Lemma lem7008138 {_128971 : Type'} (s : _128971 -> Prop) : ((term245 _128971 s) = (term246 _128971 s)) = ((term240 _128971 s) = (term265 _128971 s)).
Proof. exact (MK_COMB (@lem7008126 _128971 s) (@lem7008137 _128971 s)). Qed.
Lemma lem7008139 {_128971 : Type'} (s : _128971 -> Prop) : (term240 _128971 s) = (term265 _128971 s).
Proof. exact (EQ_MP (@lem7008138 _128971 s) (@lem7008113 _128971 s)). Qed.
Lemma lem7008140 {_128971 : Type'} (s : _128971 -> Prop) : (term198 _128971 s) = (term265 _128971 s).
Proof. exact (TRANS (@lem7008109 _128971 s) (@lem7008139 _128971 s)). Qed.
Lemma lem7008141 {_128971 : Type'} : (term209 _128971) = (term266 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008140 _128971 s)). Qed.
Lemma lem7008142 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008143 {_128971 : Type'} : (term220 _128971) = (term267 _128971).
Proof. exact (MK_COMB (@lem7008142 _128971) (@lem7008141 _128971)). Qed.
Lemma lem7008145 {A B : Type'} (P : type1413 A B) : (term241 A B P) = (term242 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7008146 {_128971 : Type'} (P : type597 _128971) : (term268 _128971 P) = (term269 _128971 P).
Proof. exact (@lem7008145 (_128971 -> Prop) (type684 _128971) P). Qed.
Lemma lem7008147 {_128971 : Type'} : (term270 _128971) = (term271 _128971).
Proof. exact (@lem7008146 _128971 (term272 _128971)). Qed.
Lemma lem7008148 {_128971 : Type'} (s : _128971 -> Prop) : (term273 _128971 s) = (term264 _128971 s).
Proof. exact (eq_refl (term273 _128971 s)). Qed.
Lemma lem7008149 {_128971 : Type'} (x : type684 _128971) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7008150 {_128971 : Type'} (s : _128971 -> Prop) (x : type684 _128971) : (term274 _128971 s x) = (term275 _128971 s x).
Proof. exact (MK_COMB (@lem7008148 _128971 s) (@lem7008149 _128971 x)). Qed.
Lemma lem7008151 {_128971 : Type'} (s : _128971 -> Prop) (x : type684 _128971) : (term275 _128971 s x) = (term262 _128971 s x).
Proof. exact (eq_refl (term275 _128971 s x)). Qed.
Lemma lem7008152 {_128971 : Type'} (s : _128971 -> Prop) (x : type684 _128971) : (term274 _128971 s x) = (term262 _128971 s x).
Proof. exact (TRANS (@lem7008150 _128971 s x) (@lem7008151 _128971 s x)). Qed.
Lemma lem7008153 {_128971 : Type'} (s : _128971 -> Prop) : (term276 _128971 s) = (term264 _128971 s).
Proof. exact (fun_ext (fun x : type684 _128971 => @lem7008152 _128971 s x)). Qed.
Lemma lem7008154 {_128971 : Type'} : (@ex ((_128971 -> Prop) -> _128971)) = (@ex ((_128971 -> Prop) -> _128971)).
Proof. exact (eq_refl (@ex ((_128971 -> Prop) -> _128971))). Qed.
Lemma lem7008155 {_128971 : Type'} (s : _128971 -> Prop) : (term277 _128971 s) = (term265 _128971 s).
Proof. exact (MK_COMB (@lem7008154 _128971) (@lem7008153 _128971 s)). Qed.
Lemma lem7008156 {_128971 : Type'} : (term278 _128971) = (term266 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008155 _128971 s)). Qed.
Lemma lem7008157 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008158 {_128971 : Type'} : (term270 _128971) = (term267 _128971).
Proof. exact (MK_COMB (@lem7008157 _128971) (@lem7008156 _128971)). Qed.
Lemma lem7008159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7008160 {_128971 : Type'} : (term279 _128971) = (term280 _128971).
Proof. exact (MK_COMB (@lem7008159) (@lem7008158 _128971)). Qed.
Lemma lem7008161 {_128971 : Type'} (s : _128971 -> Prop) : (term273 _128971 s) = (term264 _128971 s).
Proof. exact (eq_refl (term273 _128971 s)). Qed.
Lemma lem7008162 {_128971 : Type'} (x : type638 _128971) (s : _128971 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7008163 {_128971 : Type'} (x : type638 _128971) (s : _128971 -> Prop) : (term281 _128971 x s) = (term282 _128971 x s).
Proof. exact (MK_COMB (@lem7008161 _128971 s) (@lem7008162 _128971 x s)). Qed.
Lemma lem7008164 {_128971 : Type'} (x : type638 _128971) (s : _128971 -> Prop) : (term282 _128971 x s) = (term283 _128971 x s).
Proof. exact (eq_refl (term282 _128971 x s)). Qed.
Lemma lem7008165 {_128971 : Type'} (x : type638 _128971) (s : _128971 -> Prop) : (term281 _128971 x s) = (term283 _128971 x s).
Proof. exact (TRANS (@lem7008163 _128971 x s) (@lem7008164 _128971 x s)). Qed.
Lemma lem7008166 {_128971 : Type'} (x : type638 _128971) : (term284 _128971 x) = (term285 _128971 x).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008165 _128971 x s)). Qed.
Lemma lem7008167 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008168 {_128971 : Type'} (x : type638 _128971) : (term286 _128971 x) = (term287 _128971 x).
Proof. exact (MK_COMB (@lem7008167 _128971) (@lem7008166 _128971 x)). Qed.
Lemma lem7008169 {_128971 : Type'} : (term288 _128971) = (term289 _128971).
Proof. exact (fun_ext (fun x : type638 _128971 => @lem7008168 _128971 x)). Qed.
Lemma lem7008170 {_128971 : Type'} : (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971)) = (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971)).
Proof. exact (eq_refl (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971))). Qed.
Lemma lem7008171 {_128971 : Type'} : (term271 _128971) = (term290 _128971).
Proof. exact (MK_COMB (@lem7008170 _128971) (@lem7008169 _128971)). Qed.
Lemma lem7008172 {_128971 : Type'} : ((term270 _128971) = (term271 _128971)) = ((term267 _128971) = (term290 _128971)).
Proof. exact (MK_COMB (@lem7008160 _128971) (@lem7008171 _128971)). Qed.
Lemma lem7008173 {_128971 : Type'} : (term267 _128971) = (term290 _128971).
Proof. exact (EQ_MP (@lem7008172 _128971) (@lem7008147 _128971)). Qed.
Lemma lem7008174 {_128971 : Type'} : (term220 _128971) = (term290 _128971).
Proof. exact (TRANS (@lem7008143 _128971) (@lem7008173 _128971)). Qed.
Lemma lem7008175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008176 {_128971 : Type'} : (term222 _128971) = (term291 _128971).
Proof. exact (MK_COMB (@lem7008175) (@lem7008174 _128971)). Qed.
Lemma lem7008177 {_128971 : Type'} : (term225 _128971) = (term225 _128971).
Proof. exact (eq_refl (term225 _128971)). Qed.
Lemma lem7008178 {_128971 : Type'} : (term226 _128971) = (term292 _128971).
Proof. exact (MK_COMB (@lem7008176 _128971) (@lem7008177 _128971)). Qed.
Lemma lem7008180 {A : Type'} (P : A -> Prop) (Q : Prop) : (term293 A P Q) = (term294 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7008181 {_128971 : Type'} (P : type139 _128971) (Q : Prop) : (term295 _128971 P Q) = (term296 _128971 P Q).
Proof. exact (@lem7008180 (type638 _128971) P Q). Qed.
Lemma lem7008182 {_128971 : Type'} : (term297 _128971) = (term298 _128971).
Proof. exact (@lem7008181 _128971 (term289 _128971) (term225 _128971)). Qed.
Lemma lem7008183 {_128971 : Type'} (x : type638 _128971) : (term299 _128971 x) = (term287 _128971 x).
Proof. exact (eq_refl (term299 _128971 x)). Qed.
Lemma lem7008184 {_128971 : Type'} : (term300 _128971) = (term289 _128971).
Proof. exact (fun_ext (fun x : type638 _128971 => @lem7008183 _128971 x)). Qed.
Lemma lem7008185 {_128971 : Type'} : (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971)) = (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971)).
Proof. exact (eq_refl (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971))). Qed.
Lemma lem7008186 {_128971 : Type'} : (term301 _128971) = (term290 _128971).
Proof. exact (MK_COMB (@lem7008185 _128971) (@lem7008184 _128971)). Qed.
Lemma lem7008187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008188 {_128971 : Type'} : (term302 _128971) = (term291 _128971).
Proof. exact (MK_COMB (@lem7008187) (@lem7008186 _128971)). Qed.
Lemma lem7008189 {_128971 : Type'} : (term225 _128971) = (term225 _128971).
Proof. exact (eq_refl (term225 _128971)). Qed.
Lemma lem7008190 {_128971 : Type'} : (term297 _128971) = (term292 _128971).
Proof. exact (MK_COMB (@lem7008188 _128971) (@lem7008189 _128971)). Qed.
Lemma lem7008191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7008192 {_128971 : Type'} : (term303 _128971) = (term304 _128971).
Proof. exact (MK_COMB (@lem7008191) (@lem7008190 _128971)). Qed.
Lemma lem7008193 {_128971 : Type'} (x : type638 _128971) : (term299 _128971 x) = (term287 _128971 x).
Proof. exact (eq_refl (term299 _128971 x)). Qed.
Lemma lem7008194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008195 {_128971 : Type'} (x : type638 _128971) : (term305 _128971 x) = (term306 _128971 x).
Proof. exact (MK_COMB (@lem7008194) (@lem7008193 _128971 x)). Qed.
Lemma lem7008196 {_128971 : Type'} : (term225 _128971) = (term225 _128971).
Proof. exact (eq_refl (term225 _128971)). Qed.
Lemma lem7008197 {_128971 : Type'} (x : type638 _128971) : (term307 _128971 x) = (term308 _128971 x).
Proof. exact (MK_COMB (@lem7008195 _128971 x) (@lem7008196 _128971)). Qed.
Lemma lem7008198 {_128971 : Type'} : (term309 _128971) = (term310 _128971).
Proof. exact (fun_ext (fun x : type638 _128971 => @lem7008197 _128971 x)). Qed.
Lemma lem7008199 {_128971 : Type'} : (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971)) = (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971)).
Proof. exact (eq_refl (@ex ((_128971 -> Prop) -> (_128971 -> Prop) -> _128971))). Qed.
Lemma lem7008200 {_128971 : Type'} : (term298 _128971) = (term311 _128971).
Proof. exact (MK_COMB (@lem7008199 _128971) (@lem7008198 _128971)). Qed.
Lemma lem7008201 {_128971 : Type'} : ((term297 _128971) = (term298 _128971)) = ((term292 _128971) = (term311 _128971)).
Proof. exact (MK_COMB (@lem7008192 _128971) (@lem7008200 _128971)). Qed.
Lemma lem7008202 {_128971 : Type'} : (term292 _128971) = (term311 _128971).
Proof. exact (EQ_MP (@lem7008201 _128971) (@lem7008182 _128971)). Qed.
Lemma lem7008203 {_128971 : Type'} : (term226 _128971) = (term311 _128971).
Proof. exact (TRANS (@lem7008178 _128971) (@lem7008202 _128971)). Qed.
Lemma lem7008204 {_128971 : Type'} : (term180 _128971) = (term311 _128971).
Proof. exact (TRANS (@lem7008086 _128971) (@lem7008203 _128971)). Qed.
Lemma lem7008205 {_128971 : Type'} : (term23 _128971) = (term311 _128971).
Proof. exact (TRANS (@lem7007632 _128971) (@lem7008204 _128971)). Qed.
Lemma lem7008206 {_128971 : Type'} (h1 : term23 _128971) : term311 _128971.
Proof. exact (EQ_MP (@lem7008205 _128971) (@lem7007295 _128971 h1)). Qed.
Lemma lem7008214 {_128971 : Type'} (x : _128971) (t : _128971 -> Prop) : (term312 _128971 x t) = (@IN _128971 x t).
Proof. exact (@lem16933 (@IN _128971 x t)). Qed.
Lemma lem7008216 {_128971 : Type'} (x : _128971) (s : _128971 -> Prop) : (term313 _128971 x s) = (term313 _128971 x s).
Proof. exact (eq_refl (term313 _128971 x s)). Qed.
Lemma lem7008217 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term314 _128971 s x t) = (term157 _128971 s x t).
Proof. exact (MK_COMB (@lem7008216 _128971 x s) (@lem7008214 _128971 x t)). Qed.
Lemma lem7008218 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term315 _128971 s x t) = (term314 _128971 s x t).
Proof. exact (@lem17045 (@IN _128971 x s) (term316 _128971 x t)). Qed.
Lemma lem7008219 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term315 _128971 s x t) = (term157 _128971 s x t).
Proof. exact (TRANS (@lem7008218 _128971 s x t) (@lem7008217 _128971 s x t)). Qed.
Lemma lem7008225 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term317 _128971 s x t) = (term317 _128971 s x t).
Proof. exact (eq_refl (term317 _128971 s x t)). Qed.
Lemma lem7008227 {_128971 : Type'} (x : _128971) (s : _128971 -> Prop) (t : _128971 -> Prop) : (term318 _128971 x s t) = (term318 _128971 x s t).
Proof. exact (eq_refl (term318 _128971 x s t)). Qed.
Lemma lem7008228 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term319 _128971 s x t) = (term320 _128971 s x t).
Proof. exact (MK_COMB (@lem7008227 _128971 x s t) (@lem7008219 _128971 s x t)). Qed.
Lemma lem7008229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008230 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term321 _128971 s x t) = (term322 _128971 s x t).
Proof. exact (MK_COMB (@lem7008229) (@lem7008228 _128971 s x t)). Qed.
Lemma lem7008231 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term323 _128971 s x t) = (term324 _128971 s x t).
Proof. exact (MK_COMB (@lem7008230 _128971 s x t) (@lem7008225 _128971 s x t)). Qed.
Lemma lem7008232 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : ((term57 _128971 x s t) = (term58 _128971 s x t)) = (term323 _128971 s x t).
Proof. exact (@lem17784 (term57 _128971 x s t) (term58 _128971 s x t)). Qed.
Lemma lem7008233 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : ((term57 _128971 x s t) = (term58 _128971 s x t)) = (term324 _128971 s x t).
Proof. exact (TRANS (@lem7008232 _128971 s x t) (@lem7008231 _128971 s x t)). Qed.
Lemma lem7008234 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term59 _128971 s t) = (term325 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008233 _128971 s x t)). Qed.
Lemma lem7008235 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7008236 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term60 _128971 s t) = (term326 _128971 s t).
Proof. exact (MK_COMB (@lem7008235 _128971) (@lem7008234 _128971 s t)). Qed.
Lemma lem7008237 {_128971 : Type'} (s : _128971 -> Prop) : (term61 _128971 s) = (term327 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008236 _128971 s t)). Qed.
Lemma lem7008238 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008239 {_128971 : Type'} (s : _128971 -> Prop) : (term62 _128971 s) = (term328 _128971 s).
Proof. exact (MK_COMB (@lem7008238 _128971) (@lem7008237 _128971 s)). Qed.
Lemma lem7008240 {_128971 : Type'} : (term63 _128971) = (term329 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008239 _128971 s)). Qed.
Lemma lem7008241 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008242 {_128971 : Type'} : (term22 _128971) = (term330 _128971).
Proof. exact (MK_COMB (@lem7008241 _128971) (@lem7008240 _128971)). Qed.
Lemma lem7008252 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7008253 {_128971 : Type'} (P : _128971 -> Prop) (Q : _128971 -> Prop) : (term181 _128971 P Q) = (term182 _128971 P Q).
Proof. exact (@lem7008252 _128971 P Q). Qed.
Lemma lem7008254 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term331 _128971 s t) = (term332 _128971 s t).
Proof. exact (@lem7008253 _128971 (term333 _128971 s t) (term334 _128971 s t)). Qed.
Lemma lem7008255 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term335 _128971 s t x) = (term320 _128971 s x t).
Proof. exact (eq_refl (term335 _128971 s t x)). Qed.
Lemma lem7008256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008257 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term336 _128971 s t x) = (term322 _128971 s x t).
Proof. exact (MK_COMB (@lem7008256) (@lem7008255 _128971 s x t)). Qed.
Lemma lem7008258 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term337 _128971 s t x) = (term317 _128971 s x t).
Proof. exact (eq_refl (term337 _128971 s t x)). Qed.
Lemma lem7008259 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term338 _128971 s t x) = (term324 _128971 s x t).
Proof. exact (MK_COMB (@lem7008257 _128971 s x t) (@lem7008258 _128971 s x t)). Qed.
Lemma lem7008260 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term339 _128971 s t) = (term325 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008259 _128971 s x t)). Qed.
Lemma lem7008261 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7008262 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term331 _128971 s t) = (term326 _128971 s t).
Proof. exact (MK_COMB (@lem7008261 _128971) (@lem7008260 _128971 s t)). Qed.
Lemma lem7008263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7008264 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term340 _128971 s t) = (term341 _128971 s t).
Proof. exact (MK_COMB (@lem7008263) (@lem7008262 _128971 s t)). Qed.
Lemma lem7008265 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term335 _128971 s t x) = (term320 _128971 s x t).
Proof. exact (eq_refl (term335 _128971 s t x)). Qed.
Lemma lem7008266 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term342 _128971 s t) = (term333 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008265 _128971 s x t)). Qed.
Lemma lem7008267 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7008268 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term343 _128971 s t) = (term344 _128971 s t).
Proof. exact (MK_COMB (@lem7008267 _128971) (@lem7008266 _128971 s t)). Qed.
Lemma lem7008269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008270 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term345 _128971 s t) = (term346 _128971 s t).
Proof. exact (MK_COMB (@lem7008269) (@lem7008268 _128971 s t)). Qed.
Lemma lem7008271 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term337 _128971 s t x) = (term317 _128971 s x t).
Proof. exact (eq_refl (term337 _128971 s t x)). Qed.
Lemma lem7008272 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term347 _128971 s t) = (term334 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008271 _128971 s x t)). Qed.
Lemma lem7008273 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7008274 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term348 _128971 s t) = (term349 _128971 s t).
Proof. exact (MK_COMB (@lem7008273 _128971) (@lem7008272 _128971 s t)). Qed.
Lemma lem7008275 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term332 _128971 s t) = (term350 _128971 s t).
Proof. exact (MK_COMB (@lem7008270 _128971 s t) (@lem7008274 _128971 s t)). Qed.
Lemma lem7008276 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : ((term331 _128971 s t) = (term332 _128971 s t)) = ((term326 _128971 s t) = (term350 _128971 s t)).
Proof. exact (MK_COMB (@lem7008264 _128971 s t) (@lem7008275 _128971 s t)). Qed.
Lemma lem7008277 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term326 _128971 s t) = (term350 _128971 s t).
Proof. exact (EQ_MP (@lem7008276 _128971 s t) (@lem7008254 _128971 s t)). Qed.
Lemma lem7008374 {_128971 : Type'} (s : _128971 -> Prop) : (term327 _128971 s) = (term351 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008277 _128971 s t)). Qed.
Lemma lem7008375 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008376 {_128971 : Type'} (s : _128971 -> Prop) : (term328 _128971 s) = (term352 _128971 s).
Proof. exact (MK_COMB (@lem7008375 _128971) (@lem7008374 _128971 s)). Qed.
Lemma lem7008378 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7008379 {_128971 : Type'} (P : type686 _128971) (Q : type686 _128971) : (term183 _128971 P Q) = (term184 _128971 P Q).
Proof. exact (@lem7008378 (_128971 -> Prop) P Q). Qed.
Lemma lem7008380 {_128971 : Type'} (s : _128971 -> Prop) : (term353 _128971 s) = (term354 _128971 s).
Proof. exact (@lem7008379 _128971 (term355 _128971 s) (term356 _128971 s)). Qed.
Lemma lem7008381 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term357 _128971 s t) = (term344 _128971 s t).
Proof. exact (eq_refl (term357 _128971 s t)). Qed.
Lemma lem7008382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008383 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term358 _128971 s t) = (term346 _128971 s t).
Proof. exact (MK_COMB (@lem7008382) (@lem7008381 _128971 s t)). Qed.
Lemma lem7008384 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term359 _128971 s t) = (term349 _128971 s t).
Proof. exact (eq_refl (term359 _128971 s t)). Qed.
Lemma lem7008385 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term360 _128971 s t) = (term350 _128971 s t).
Proof. exact (MK_COMB (@lem7008383 _128971 s t) (@lem7008384 _128971 s t)). Qed.
Lemma lem7008386 {_128971 : Type'} (s : _128971 -> Prop) : (term361 _128971 s) = (term351 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008385 _128971 s t)). Qed.
Lemma lem7008387 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008388 {_128971 : Type'} (s : _128971 -> Prop) : (term353 _128971 s) = (term352 _128971 s).
Proof. exact (MK_COMB (@lem7008387 _128971) (@lem7008386 _128971 s)). Qed.
Lemma lem7008389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7008390 {_128971 : Type'} (s : _128971 -> Prop) : (term362 _128971 s) = (term363 _128971 s).
Proof. exact (MK_COMB (@lem7008389) (@lem7008388 _128971 s)). Qed.
Lemma lem7008391 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term357 _128971 s t) = (term344 _128971 s t).
Proof. exact (eq_refl (term357 _128971 s t)). Qed.
Lemma lem7008392 {_128971 : Type'} (s : _128971 -> Prop) : (term364 _128971 s) = (term355 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008391 _128971 s t)). Qed.
Lemma lem7008393 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008394 {_128971 : Type'} (s : _128971 -> Prop) : (term365 _128971 s) = (term366 _128971 s).
Proof. exact (MK_COMB (@lem7008393 _128971) (@lem7008392 _128971 s)). Qed.
Lemma lem7008395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008396 {_128971 : Type'} (s : _128971 -> Prop) : (term367 _128971 s) = (term368 _128971 s).
Proof. exact (MK_COMB (@lem7008395) (@lem7008394 _128971 s)). Qed.
Lemma lem7008397 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term359 _128971 s t) = (term349 _128971 s t).
Proof. exact (eq_refl (term359 _128971 s t)). Qed.
Lemma lem7008398 {_128971 : Type'} (s : _128971 -> Prop) : (term369 _128971 s) = (term356 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008397 _128971 s t)). Qed.
Lemma lem7008399 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008400 {_128971 : Type'} (s : _128971 -> Prop) : (term370 _128971 s) = (term371 _128971 s).
Proof. exact (MK_COMB (@lem7008399 _128971) (@lem7008398 _128971 s)). Qed.
Lemma lem7008401 {_128971 : Type'} (s : _128971 -> Prop) : (term354 _128971 s) = (term372 _128971 s).
Proof. exact (MK_COMB (@lem7008396 _128971 s) (@lem7008400 _128971 s)). Qed.
Lemma lem7008402 {_128971 : Type'} (s : _128971 -> Prop) : ((term353 _128971 s) = (term354 _128971 s)) = ((term352 _128971 s) = (term372 _128971 s)).
Proof. exact (MK_COMB (@lem7008390 _128971 s) (@lem7008401 _128971 s)). Qed.
Lemma lem7008403 {_128971 : Type'} (s : _128971 -> Prop) : (term352 _128971 s) = (term372 _128971 s).
Proof. exact (EQ_MP (@lem7008402 _128971 s) (@lem7008380 _128971 s)). Qed.
Lemma lem7008508 {_128971 : Type'} (s : _128971 -> Prop) : (term328 _128971 s) = (term372 _128971 s).
Proof. exact (TRANS (@lem7008376 _128971 s) (@lem7008403 _128971 s)). Qed.
Lemma lem7008509 {_128971 : Type'} : (term329 _128971) = (term373 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008508 _128971 s)). Qed.
Lemma lem7008510 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008511 {_128971 : Type'} : (term330 _128971) = (term374 _128971).
Proof. exact (MK_COMB (@lem7008510 _128971) (@lem7008509 _128971)). Qed.
Lemma lem7008513 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7008514 {_128971 : Type'} (P : type686 _128971) (Q : type686 _128971) : (term183 _128971 P Q) = (term184 _128971 P Q).
Proof. exact (@lem7008513 (_128971 -> Prop) P Q). Qed.
Lemma lem7008515 {_128971 : Type'} : (term375 _128971) = (term376 _128971).
Proof. exact (@lem7008514 _128971 (term377 _128971) (term378 _128971)). Qed.
Lemma lem7008516 {_128971 : Type'} (s : _128971 -> Prop) : (term379 _128971 s) = (term366 _128971 s).
Proof. exact (eq_refl (term379 _128971 s)). Qed.
Lemma lem7008517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008518 {_128971 : Type'} (s : _128971 -> Prop) : (term380 _128971 s) = (term368 _128971 s).
Proof. exact (MK_COMB (@lem7008517) (@lem7008516 _128971 s)). Qed.
Lemma lem7008519 {_128971 : Type'} (s : _128971 -> Prop) : (term381 _128971 s) = (term371 _128971 s).
Proof. exact (eq_refl (term381 _128971 s)). Qed.
Lemma lem7008520 {_128971 : Type'} (s : _128971 -> Prop) : (term382 _128971 s) = (term372 _128971 s).
Proof. exact (MK_COMB (@lem7008518 _128971 s) (@lem7008519 _128971 s)). Qed.
Lemma lem7008521 {_128971 : Type'} : (term383 _128971) = (term373 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008520 _128971 s)). Qed.
Lemma lem7008522 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008523 {_128971 : Type'} : (term375 _128971) = (term374 _128971).
Proof. exact (MK_COMB (@lem7008522 _128971) (@lem7008521 _128971)). Qed.
Lemma lem7008524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7008525 {_128971 : Type'} : (term384 _128971) = (term385 _128971).
Proof. exact (MK_COMB (@lem7008524) (@lem7008523 _128971)). Qed.
Lemma lem7008526 {_128971 : Type'} (s : _128971 -> Prop) : (term379 _128971 s) = (term366 _128971 s).
Proof. exact (eq_refl (term379 _128971 s)). Qed.
Lemma lem7008527 {_128971 : Type'} : (term386 _128971) = (term377 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008526 _128971 s)). Qed.
Lemma lem7008528 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008529 {_128971 : Type'} : (term387 _128971) = (term388 _128971).
Proof. exact (MK_COMB (@lem7008528 _128971) (@lem7008527 _128971)). Qed.
Lemma lem7008530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008531 {_128971 : Type'} : (term389 _128971) = (term390 _128971).
Proof. exact (MK_COMB (@lem7008530) (@lem7008529 _128971)). Qed.
Lemma lem7008532 {_128971 : Type'} (s : _128971 -> Prop) : (term381 _128971 s) = (term371 _128971 s).
Proof. exact (eq_refl (term381 _128971 s)). Qed.
Lemma lem7008533 {_128971 : Type'} : (term391 _128971) = (term378 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008532 _128971 s)). Qed.
Lemma lem7008534 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008535 {_128971 : Type'} : (term392 _128971) = (term393 _128971).
Proof. exact (MK_COMB (@lem7008534 _128971) (@lem7008533 _128971)). Qed.
Lemma lem7008536 {_128971 : Type'} : (term376 _128971) = (term394 _128971).
Proof. exact (MK_COMB (@lem7008531 _128971) (@lem7008535 _128971)). Qed.
Lemma lem7008537 {_128971 : Type'} : ((term375 _128971) = (term376 _128971)) = ((term374 _128971) = (term394 _128971)).
Proof. exact (MK_COMB (@lem7008525 _128971) (@lem7008536 _128971)). Qed.
Lemma lem7008538 {_128971 : Type'} : (term374 _128971) = (term394 _128971).
Proof. exact (EQ_MP (@lem7008537 _128971) (@lem7008515 _128971)). Qed.
Lemma lem7008653 {_128971 : Type'} : (term330 _128971) = (term394 _128971).
Proof. exact (TRANS (@lem7008511 _128971) (@lem7008538 _128971)). Qed.
Lemma lem7008654 {_128971 : Type'} : (term22 _128971) = (term394 _128971).
Proof. exact (TRANS (@lem7008242 _128971) (@lem7008653 _128971)). Qed.
Lemma lem7008655 {_128971 : Type'} (h1 : term22 _128971) : term394 _128971.
Proof. exact (EQ_MP (@lem7008654 _128971) (@lem7007296 _128971 h1)). Qed.
Lemma lem7008656 {_128971 : Type'} (x : type638 _128971) (h1 : term308 _128971 x) : term308 _128971 x.
Proof. exact (h1). Qed.
Lemma lem7008661 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7008667 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7008670 {_128971 : Type'} (s : _128971 -> Prop) : (@FINITE _128971 s) = (@FINITE _128971 s).
Proof. exact (eq_refl (@FINITE _128971 s)). Qed.
Lemma lem7008685 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term126 _128971 s t) = (term126 _128971 s t).
Proof. exact (eq_refl (term126 _128971 s t)). Qed.
Lemma lem7008686 {_128971 : Type'} (s : _128971 -> Prop) : (term141 _128971 s) = (term141 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008685 _128971 s t)). Qed.
Lemma lem7008687 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008688 {_128971 : Type'} (s : _128971 -> Prop) : (term150 _128971 s) = (term150 _128971 s).
Proof. exact (MK_COMB (@lem7008687 _128971) (@lem7008686 _128971 s)). Qed.
Lemma lem7008689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7008690 {_128971 : Type'} (s : _128971 -> Prop) : (term152 _128971 s) = (term152 _128971 s).
Proof. exact (MK_COMB (@lem7008689) (@lem7008688 _128971 s)). Qed.
Lemma lem7008691 {_128971 : Type'} (s : _128971 -> Prop) : (term153 _128971 s) = (term153 _128971 s).
Proof. exact (MK_COMB (@lem7008690 _128971 s) (@lem7008670 _128971 s)). Qed.
Lemma lem7008692 {_128971 : Type'} : (term154 _128971) = (term154 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008691 _128971 s)). Qed.
Lemma lem7008693 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008694 {_128971 : Type'} : (term155 _128971) = (term155 _128971).
Proof. exact (MK_COMB (@lem7008693 _128971) (@lem7008692 _128971)). Qed.
Lemma lem7008695 {_128971 : Type'} (h1 : term24 _128971) : term155 _128971.
Proof. exact (EQ_MP (@lem7008694 _128971) (@lem7007586 _128971 h1)). Qed.
Lemma lem7008724 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term317 _128971 s x t) = (term317 _128971 s x t).
Proof. exact (eq_refl (term317 _128971 s x t)). Qed.
Lemma lem7008725 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term334 _128971 s t) = (term334 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008724 _128971 s x t)). Qed.
Lemma lem7008726 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7008727 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term349 _128971 s t) = (term349 _128971 s t).
Proof. exact (MK_COMB (@lem7008726 _128971) (@lem7008725 _128971 s t)). Qed.
Lemma lem7008728 {_128971 : Type'} (s : _128971 -> Prop) : (term356 _128971 s) = (term356 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008727 _128971 s t)). Qed.
Lemma lem7008729 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008730 {_128971 : Type'} (s : _128971 -> Prop) : (term371 _128971 s) = (term371 _128971 s).
Proof. exact (MK_COMB (@lem7008729 _128971) (@lem7008728 _128971 s)). Qed.
Lemma lem7008731 {_128971 : Type'} : (term378 _128971) = (term378 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008730 _128971 s)). Qed.
Lemma lem7008732 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008733 {_128971 : Type'} : (term393 _128971) = (term393 _128971).
Proof. exact (MK_COMB (@lem7008732 _128971) (@lem7008731 _128971)). Qed.
Lemma lem7008760 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term320 _128971 s x t) = (term320 _128971 s x t).
Proof. exact (eq_refl (term320 _128971 s x t)). Qed.
Lemma lem7008761 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term333 _128971 s t) = (term333 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008760 _128971 s x t)). Qed.
Lemma lem7008762 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7008763 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term344 _128971 s t) = (term344 _128971 s t).
Proof. exact (MK_COMB (@lem7008762 _128971) (@lem7008761 _128971 s t)). Qed.
Lemma lem7008764 {_128971 : Type'} (s : _128971 -> Prop) : (term355 _128971 s) = (term355 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008763 _128971 s t)). Qed.
Lemma lem7008765 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008766 {_128971 : Type'} (s : _128971 -> Prop) : (term366 _128971 s) = (term366 _128971 s).
Proof. exact (MK_COMB (@lem7008765 _128971) (@lem7008764 _128971 s)). Qed.
Lemma lem7008767 {_128971 : Type'} : (term377 _128971) = (term377 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008766 _128971 s)). Qed.
Lemma lem7008768 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008769 {_128971 : Type'} : (term388 _128971) = (term388 _128971).
Proof. exact (MK_COMB (@lem7008768 _128971) (@lem7008767 _128971)). Qed.
Lemma lem7008770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008771 {_128971 : Type'} : (term390 _128971) = (term390 _128971).
Proof. exact (MK_COMB (@lem7008770) (@lem7008769 _128971)). Qed.
Lemma lem7008772 {_128971 : Type'} : (term394 _128971) = (term394 _128971).
Proof. exact (MK_COMB (@lem7008771 _128971) (@lem7008733 _128971)). Qed.
Lemma lem7008773 {_128971 : Type'} (h1 : term22 _128971) : term394 _128971.
Proof. exact (EQ_MP (@lem7008772 _128971) (@lem7008655 _128971 h1)). Qed.
Lemma lem7008788 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term157 _128971 s x t) = (term157 _128971 s x t).
Proof. exact (eq_refl (term157 _128971 s x t)). Qed.
Lemma lem7008789 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term165 _128971 s t) = (term165 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7008788 _128971 s x t)). Qed.
Lemma lem7008790 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7008791 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term166 _128971 s t) = (term166 _128971 s t).
Proof. exact (MK_COMB (@lem7008790 _128971) (@lem7008789 _128971 s t)). Qed.
Lemma lem7008800 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term167 _128971 s t) = (term167 _128971 s t).
Proof. exact (eq_refl (term167 _128971 s t)). Qed.
Lemma lem7008801 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term169 _128971 s t) = (term169 _128971 s t).
Proof. exact (MK_COMB (@lem7008800 _128971 s t) (@lem7008791 _128971 s t)). Qed.
Lemma lem7008802 {_128971 : Type'} (s : _128971 -> Prop) : (term188 _128971 s) = (term188 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008801 _128971 s t)). Qed.
Lemma lem7008803 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008804 {_128971 : Type'} (s : _128971 -> Prop) : (term203 _128971 s) = (term203 _128971 s).
Proof. exact (MK_COMB (@lem7008803 _128971) (@lem7008802 _128971 s)). Qed.
Lemma lem7008805 {_128971 : Type'} : (term210 _128971) = (term210 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008804 _128971 s)). Qed.
Lemma lem7008806 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008807 {_128971 : Type'} : (term225 _128971) = (term225 _128971).
Proof. exact (MK_COMB (@lem7008806 _128971) (@lem7008805 _128971)). Qed.
Lemma lem7008838 {_128971 : Type'} (x : type638 _128971) (s : _128971 -> Prop) (t : _128971 -> Prop) : (term395 _128971 x s t) = (term395 _128971 x s t).
Proof. exact (eq_refl (term395 _128971 x s t)). Qed.
Lemma lem7008839 {_128971 : Type'} (x : type638 _128971) (s : _128971 -> Prop) : (term396 _128971 x s) = (term396 _128971 x s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008838 _128971 x s t)). Qed.
Lemma lem7008840 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008841 {_128971 : Type'} (x : type638 _128971) (s : _128971 -> Prop) : (term283 _128971 x s) = (term283 _128971 x s).
Proof. exact (MK_COMB (@lem7008840 _128971) (@lem7008839 _128971 x s)). Qed.
Lemma lem7008842 {_128971 : Type'} (x : type638 _128971) : (term285 _128971 x) = (term285 _128971 x).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008841 _128971 x s)). Qed.
Lemma lem7008843 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008844 {_128971 : Type'} (x : type638 _128971) : (term287 _128971 x) = (term287 _128971 x).
Proof. exact (MK_COMB (@lem7008843 _128971) (@lem7008842 _128971 x)). Qed.
Lemma lem7008845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7008846 {_128971 : Type'} (x : type638 _128971) : (term306 _128971 x) = (term306 _128971 x).
Proof. exact (MK_COMB (@lem7008845) (@lem7008844 _128971 x)). Qed.
Lemma lem7008847 {_128971 : Type'} (x : type638 _128971) : (term308 _128971 x) = (term308 _128971 x).
Proof. exact (MK_COMB (@lem7008846 _128971 x) (@lem7008807 _128971)). Qed.
Lemma lem7008848 {_128971 : Type'} (x : type638 _128971) (h1 : term308 _128971 x) : term308 _128971 x.
Proof. exact (EQ_MP (@lem7008847 _128971 x) (@lem7008656 _128971 x h1)). Qed.
Lemma lem7008888 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term121 _128971 u v f x') : term121 _128971 u v f x'.
Proof. exact (h1). Qed.
Lemma lem7008889 {_128971 : Type'} (x : type638 _128971) (h1 : term308 _128971 x) : term225 _128971.
Proof. exact (proj2 (@lem7008848 _128971 x h1)). Qed.
Lemma lem7008891 {_128971 : Type'} (h1 : term22 _128971) : term393 _128971.
Proof. exact (proj2 (@lem7008773 _128971 h1)). Qed.
Lemma lem7008894 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term108 _128971 u v f x') : term108 _128971 u v f x'.
Proof. exact (h1). Qed.
Lemma lem7008896 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term81 _128971 u v f x') : term81 _128971 u v f x'.
Proof. exact (h1). Qed.
Lemma lem7008902 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7008906 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7008908 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7008909 {_128971 : Type'} (P : type686 _128971) (Q : Prop) : (term138 _128971 P Q) = (term137 _128971 P Q).
Proof. exact (@lem7008908 (_128971 -> Prop) P Q). Qed.
Lemma lem7008910 {_128971 : Type'} (s : _128971 -> Prop) : (term140 _128971 s) = (term139 _128971 s).
Proof. exact (@lem7008909 _128971 (term141 _128971 s) (@FINITE _128971 s)). Qed.
Lemma lem7008911 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term142 _128971 s t) = (term126 _128971 s t).
Proof. exact (eq_refl (term142 _128971 s t)). Qed.
Lemma lem7008912 {_128971 : Type'} (s : _128971 -> Prop) : (term148 _128971 s) = (term141 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008911 _128971 s t)). Qed.
Lemma lem7008913 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008914 {_128971 : Type'} (s : _128971 -> Prop) : (term149 _128971 s) = (term150 _128971 s).
Proof. exact (MK_COMB (@lem7008913 _128971) (@lem7008912 _128971 s)). Qed.
Lemma lem7008915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7008916 {_128971 : Type'} (s : _128971 -> Prop) : (term151 _128971 s) = (term152 _128971 s).
Proof. exact (MK_COMB (@lem7008915) (@lem7008914 _128971 s)). Qed.
Lemma lem7008917 {_128971 : Type'} (s : _128971 -> Prop) : (@FINITE _128971 s) = (@FINITE _128971 s).
Proof. exact (eq_refl (@FINITE _128971 s)). Qed.
Lemma lem7008918 {_128971 : Type'} (s : _128971 -> Prop) : (term140 _128971 s) = (term153 _128971 s).
Proof. exact (MK_COMB (@lem7008916 _128971 s) (@lem7008917 _128971 s)). Qed.
Lemma lem7008919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7008920 {_128971 : Type'} (s : _128971 -> Prop) : (term397 _128971 s) = (term398 _128971 s).
Proof. exact (MK_COMB (@lem7008919) (@lem7008918 _128971 s)). Qed.
Lemma lem7008921 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term142 _128971 s t) = (term126 _128971 s t).
Proof. exact (eq_refl (term142 _128971 s t)). Qed.
Lemma lem7008922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7008923 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term143 _128971 s t) = (term128 _128971 s t).
Proof. exact (MK_COMB (@lem7008922) (@lem7008921 _128971 s t)). Qed.
Lemma lem7008924 {_128971 : Type'} (s : _128971 -> Prop) : (@FINITE _128971 s) = (@FINITE _128971 s).
Proof. exact (eq_refl (@FINITE _128971 s)). Qed.
Lemma lem7008925 {_128971 : Type'} (t : _128971 -> Prop) (s : _128971 -> Prop) : (term144 _128971 t s) = (term130 _128971 t s).
Proof. exact (MK_COMB (@lem7008923 _128971 s t) (@lem7008924 _128971 s)). Qed.
Lemma lem7008926 {_128971 : Type'} (s : _128971 -> Prop) : (term145 _128971 s) = (term131 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008925 _128971 t s)). Qed.
Lemma lem7008927 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008928 {_128971 : Type'} (s : _128971 -> Prop) : (term139 _128971 s) = (term132 _128971 s).
Proof. exact (MK_COMB (@lem7008927 _128971) (@lem7008926 _128971 s)). Qed.
Lemma lem7008929 {_128971 : Type'} (s : _128971 -> Prop) : ((term140 _128971 s) = (term139 _128971 s)) = ((term153 _128971 s) = (term132 _128971 s)).
Proof. exact (MK_COMB (@lem7008920 _128971 s) (@lem7008928 _128971 s)). Qed.
Lemma lem7008930 {_128971 : Type'} (s : _128971 -> Prop) : (term153 _128971 s) = (term132 _128971 s).
Proof. exact (EQ_MP (@lem7008929 _128971 s) (@lem7008910 _128971 s)). Qed.
Lemma lem7008931 {_128971 : Type'} : (term154 _128971) = (term133 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008930 _128971 s)). Qed.
Lemma lem7008932 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008933 {_128971 : Type'} : (term155 _128971) = (term134 _128971).
Proof. exact (MK_COMB (@lem7008932 _128971) (@lem7008931 _128971)). Qed.
Lemma lem7008946 {_128971 : Type'} (t : _128971 -> Prop) (s : _128971 -> Prop) : (term130 _128971 t s) = (term130 _128971 t s).
Proof. exact (eq_refl (term130 _128971 t s)). Qed.
Lemma lem7008947 {_128971 : Type'} (s : _128971 -> Prop) : (term131 _128971 s) = (term131 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7008946 _128971 t s)). Qed.
Lemma lem7008948 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008949 {_128971 : Type'} (s : _128971 -> Prop) : (term132 _128971 s) = (term132 _128971 s).
Proof. exact (MK_COMB (@lem7008948 _128971) (@lem7008947 _128971 s)). Qed.
Lemma lem7008950 {_128971 : Type'} : (term133 _128971) = (term133 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7008949 _128971 s)). Qed.
Lemma lem7008951 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7008952 {_128971 : Type'} : (term134 _128971) = (term134 _128971).
Proof. exact (MK_COMB (@lem7008951 _128971) (@lem7008950 _128971)). Qed.
Lemma lem7008953 {_128971 : Type'} : (term155 _128971) = (term134 _128971).
Proof. exact (TRANS (@lem7008933 _128971) (@lem7008952 _128971)). Qed.
Lemma lem7008954 {_128971 : Type'} (h1 : term24 _128971) : term134 _128971.
Proof. exact (EQ_MP (@lem7008953 _128971) (@lem7008695 _128971 h1)). Qed.
Lemma lem7009088 {_128971 : Type'} (u : _128971 -> Prop) (h1 : term101 _128971 u) : term101 _128971 u.
Proof. exact (h1). Qed.
Lemma lem7009092 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7009278 {_128971 : Type'} (v : _128971 -> Prop) (h1 : term101 _128971 v) : term101 _128971 v.
Proof. exact (h1). Qed.
Lemma lem7009286 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7009362 {A : Type'} (P : Prop) (Q : A -> Prop) : (term399 A P Q) = (term400 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7009363 {_128971 : Type'} (P : Prop) (Q : _128971 -> Prop) : (term399 _128971 P Q) = (term400 _128971 P Q).
Proof. exact (@lem7009362 _128971 P Q). Qed.
Lemma lem7009364 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term401 _128971 s t) = (term402 _128971 s t).
Proof. exact (@lem7009363 _128971 (term403 _128971 s t) (term165 _128971 s t)). Qed.
Lemma lem7009365 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term404 _128971 s t x) = (term157 _128971 s x t).
Proof. exact (eq_refl (term404 _128971 s t x)). Qed.
Lemma lem7009366 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term405 _128971 s t) = (term165 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7009365 _128971 s x t)). Qed.
Lemma lem7009367 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7009368 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term406 _128971 s t) = (term166 _128971 s t).
Proof. exact (MK_COMB (@lem7009367 _128971) (@lem7009366 _128971 s t)). Qed.
Lemma lem7009369 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term167 _128971 s t) = (term167 _128971 s t).
Proof. exact (eq_refl (term167 _128971 s t)). Qed.
Lemma lem7009370 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term401 _128971 s t) = (term169 _128971 s t).
Proof. exact (MK_COMB (@lem7009369 _128971 s t) (@lem7009368 _128971 s t)). Qed.
Lemma lem7009371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7009372 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term407 _128971 s t) = (term408 _128971 s t).
Proof. exact (MK_COMB (@lem7009371) (@lem7009370 _128971 s t)). Qed.
Lemma lem7009373 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term404 _128971 s t x) = (term157 _128971 s x t).
Proof. exact (eq_refl (term404 _128971 s t x)). Qed.
Lemma lem7009374 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term167 _128971 s t) = (term167 _128971 s t).
Proof. exact (eq_refl (term167 _128971 s t)). Qed.
Lemma lem7009375 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term409 _128971 s t x) = (term410 _128971 s x t).
Proof. exact (MK_COMB (@lem7009374 _128971 s t) (@lem7009373 _128971 s x t)). Qed.
Lemma lem7009376 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term411 _128971 s t) = (term412 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7009375 _128971 s x t)). Qed.
Lemma lem7009377 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7009378 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term402 _128971 s t) = (term413 _128971 s t).
Proof. exact (MK_COMB (@lem7009377 _128971) (@lem7009376 _128971 s t)). Qed.
Lemma lem7009379 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : ((term401 _128971 s t) = (term402 _128971 s t)) = ((term169 _128971 s t) = (term413 _128971 s t)).
Proof. exact (MK_COMB (@lem7009372 _128971 s t) (@lem7009378 _128971 s t)). Qed.
Lemma lem7009380 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term169 _128971 s t) = (term413 _128971 s t).
Proof. exact (EQ_MP (@lem7009379 _128971 s t) (@lem7009364 _128971 s t)). Qed.
Lemma lem7009381 {_128971 : Type'} (s : _128971 -> Prop) : (term188 _128971 s) = (term414 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7009380 _128971 s t)). Qed.
Lemma lem7009382 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7009383 {_128971 : Type'} (s : _128971 -> Prop) : (term203 _128971 s) = (term415 _128971 s).
Proof. exact (MK_COMB (@lem7009382 _128971) (@lem7009381 _128971 s)). Qed.
Lemma lem7009384 {_128971 : Type'} : (term210 _128971) = (term416 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7009383 _128971 s)). Qed.
Lemma lem7009385 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7009386 {_128971 : Type'} : (term225 _128971) = (term417 _128971).
Proof. exact (MK_COMB (@lem7009385 _128971) (@lem7009384 _128971)). Qed.
Lemma lem7009399 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term410 _128971 s x t) = (term410 _128971 s x t).
Proof. exact (eq_refl (term410 _128971 s x t)). Qed.
Lemma lem7009400 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term412 _128971 s t) = (term412 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7009399 _128971 s x t)). Qed.
Lemma lem7009401 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7009402 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term413 _128971 s t) = (term413 _128971 s t).
Proof. exact (MK_COMB (@lem7009401 _128971) (@lem7009400 _128971 s t)). Qed.
Lemma lem7009403 {_128971 : Type'} (s : _128971 -> Prop) : (term414 _128971 s) = (term414 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7009402 _128971 s t)). Qed.
Lemma lem7009404 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7009405 {_128971 : Type'} (s : _128971 -> Prop) : (term415 _128971 s) = (term415 _128971 s).
Proof. exact (MK_COMB (@lem7009404 _128971) (@lem7009403 _128971 s)). Qed.
Lemma lem7009406 {_128971 : Type'} : (term416 _128971) = (term416 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7009405 _128971 s)). Qed.
Lemma lem7009407 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7009408 {_128971 : Type'} : (term417 _128971) = (term417 _128971).
Proof. exact (MK_COMB (@lem7009407 _128971) (@lem7009406 _128971)). Qed.
Lemma lem7009409 {_128971 : Type'} : (term225 _128971) = (term417 _128971).
Proof. exact (TRANS (@lem7009386 _128971) (@lem7009408 _128971)). Qed.
Lemma lem7009410 {_128971 : Type'} (x : type638 _128971) (h1 : term308 _128971 x) : term417 _128971.
Proof. exact (EQ_MP (@lem7009409 _128971) (@lem7008889 _128971 x h1)). Qed.
Lemma lem7009453 {_128971 : Type'} (s : _128971 -> Prop) (x : _128971) (t : _128971 -> Prop) : (term317 _128971 s x t) = (term418 _128971 s x t).
Proof. exact (@lem19490 (@IN _128971 x s) (term419 _128971 x s t) (term316 _128971 x t)). Qed.
Lemma lem7009454 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term334 _128971 s t) = (term420 _128971 s t).
Proof. exact (fun_ext (fun x : _128971 => @lem7009453 _128971 s x t)). Qed.
Lemma lem7009455 {_128971 : Type'} : (@all _128971) = (@all _128971).
Proof. exact (eq_refl (@all _128971)). Qed.
Lemma lem7009456 {_128971 : Type'} (s : _128971 -> Prop) (t : _128971 -> Prop) : (term349 _128971 s t) = (term421 _128971 s t).
Proof. exact (MK_COMB (@lem7009455 _128971) (@lem7009454 _128971 s t)). Qed.
Lemma lem7009457 {_128971 : Type'} (s : _128971 -> Prop) : (term356 _128971 s) = (term422 _128971 s).
Proof. exact (fun_ext (fun t : _128971 -> Prop => @lem7009456 _128971 s t)). Qed.
Lemma lem7009458 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7009459 {_128971 : Type'} (s : _128971 -> Prop) : (term371 _128971 s) = (term423 _128971 s).
Proof. exact (MK_COMB (@lem7009458 _128971) (@lem7009457 _128971 s)). Qed.
Lemma lem7009460 {_128971 : Type'} : (term378 _128971) = (term424 _128971).
Proof. exact (fun_ext (fun s : _128971 -> Prop => @lem7009459 _128971 s)). Qed.
Lemma lem7009461 {_128971 : Type'} : (@all (_128971 -> Prop)) = (@all (_128971 -> Prop)).
Proof. exact (eq_refl (@all (_128971 -> Prop))). Qed.
Lemma lem7009463 {_128971 : Type'} : (term393 _128971) = (term425 _128971).
Proof. exact (MK_COMB (@lem7009461 _128971) (@lem7009460 _128971)). Qed.
Lemma lem7009464 {_128971 : Type'} (h1 : term22 _128971) : term425 _128971.
Proof. exact (EQ_MP (@lem7009463 _128971) (@lem7008891 _128971 h1)). Qed.
Lemma lem7009473 {_128971 : Type'} (_93493 : _128971 -> Prop) (h1 : term24 _128971) : term426 _128971 _93493.
Proof. exact (@lem7008954 _128971 h1 _93493). Qed.
Lemma lem7009474 {_128971 : Type'} (_93493 : _128971 -> Prop) : (term426 _128971 _93493) = (term132 _128971 _93493).
Proof. exact (eq_refl (term426 _128971 _93493)). Qed.
Lemma lem7009475 {_128971 : Type'} (_93493 : _128971 -> Prop) (h1 : term24 _128971) : term132 _128971 _93493.
Proof. exact (EQ_MP (@lem7009474 _128971 _93493) (@lem7009473 _128971 _93493 h1)). Qed.
Lemma lem7009476 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) (h1 : term24 _128971) : term427 _128971 _93493 _93494.
Proof. exact (@lem7009475 _128971 _93493 h1 _93494). Qed.
Lemma lem7009477 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) : (term427 _128971 _93493 _93494) = (term130 _128971 _93494 _93493).
Proof. exact (eq_refl (term427 _128971 _93493 _93494)). Qed.
Lemma lem7009478 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) (h1 : term24 _128971) : term130 _128971 _93494 _93493.
Proof. exact (EQ_MP (@lem7009477 _128971 _93494 _93493) (@lem7009476 _128971 _93493 _93494 h1)). Qed.
Lemma lem7009563 {_128971 : Type'} (_93523 : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term428 _128971 _93523.
Proof. exact (@lem7009410 _128971 x h1 _93523). Qed.
Lemma lem7009564 {_128971 : Type'} (_93523 : _128971 -> Prop) : (term428 _128971 _93523) = (term415 _128971 _93523).
Proof. exact (eq_refl (term428 _128971 _93523)). Qed.
Lemma lem7009565 {_128971 : Type'} (_93523 : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term415 _128971 _93523.
Proof. exact (EQ_MP (@lem7009564 _128971 _93523) (@lem7009563 _128971 _93523 x h1)). Qed.
Lemma lem7009566 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term429 _128971 _93523 _93524.
Proof. exact (@lem7009565 _128971 _93523 x h1 _93524). Qed.
Lemma lem7009567 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term429 _128971 _93523 _93524) = (term413 _128971 _93523 _93524).
Proof. exact (eq_refl (term429 _128971 _93523 _93524)). Qed.
Lemma lem7009568 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term413 _128971 _93523 _93524.
Proof. exact (EQ_MP (@lem7009567 _128971 _93523 _93524) (@lem7009566 _128971 _93523 _93524 x h1)). Qed.
Lemma lem7009569 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) (_93525 : _128971) (x : type638 _128971) (h1 : term308 _128971 x) : term430 _128971 _93523 _93524 _93525.
Proof. exact (@lem7009568 _128971 _93523 _93524 x h1 _93525). Qed.
Lemma lem7009570 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93525 : _128971) (_93524 : _128971 -> Prop) : (term430 _128971 _93523 _93524 _93525) = (term410 _128971 _93523 _93525 _93524).
Proof. exact (eq_refl (term430 _128971 _93523 _93524 _93525)). Qed.
Lemma lem7009581 {_128971 : Type'} (_93529 : _128971 -> Prop) (h1 : term22 _128971) : term431 _128971 _93529.
Proof. exact (@lem7009464 _128971 h1 _93529). Qed.
Lemma lem7009582 {_128971 : Type'} (_93529 : _128971 -> Prop) : (term431 _128971 _93529) = (term423 _128971 _93529).
Proof. exact (eq_refl (term431 _128971 _93529)). Qed.
Lemma lem7009583 {_128971 : Type'} (_93529 : _128971 -> Prop) (h1 : term22 _128971) : term423 _128971 _93529.
Proof. exact (EQ_MP (@lem7009582 _128971 _93529) (@lem7009581 _128971 _93529 h1)). Qed.
Lemma lem7009584 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) (h1 : term22 _128971) : term432 _128971 _93529 _93530.
Proof. exact (@lem7009583 _128971 _93529 h1 _93530). Qed.
Lemma lem7009585 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : (term432 _128971 _93529 _93530) = (term421 _128971 _93529 _93530).
Proof. exact (eq_refl (term432 _128971 _93529 _93530)). Qed.
Lemma lem7009586 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) (h1 : term22 _128971) : term421 _128971 _93529 _93530.
Proof. exact (EQ_MP (@lem7009585 _128971 _93529 _93530) (@lem7009584 _128971 _93529 _93530 h1)). Qed.
Lemma lem7009587 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) (_93531 : _128971) (h1 : term22 _128971) : term433 _128971 _93529 _93530 _93531.
Proof. exact (@lem7009586 _128971 _93529 _93530 h1 _93531). Qed.
Lemma lem7009588 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93531 : _128971) (_93530 : _128971 -> Prop) : (term433 _128971 _93529 _93530 _93531) = (term418 _128971 _93529 _93531 _93530).
Proof. exact (eq_refl (term433 _128971 _93529 _93530 _93531)). Qed.
Lemma lem7009589 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93531 : _128971) (_93530 : _128971 -> Prop) (h1 : term22 _128971) : term418 _128971 _93529 _93531 _93530.
Proof. exact (EQ_MP (@lem7009588 _128971 _93529 _93531 _93530) (@lem7009587 _128971 _93529 _93530 _93531 h1)). Qed.
Lemma lem7009603 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7009605 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7009616 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) : (term130 _128971 _93494 _93493) = (term434 _128971 _93494 _93493).
Proof. exact (@lem7006908 (term101 _128971 _93494) (term403 _128971 _93493 _93494) (@FINITE _128971 _93493)). Qed.
Lemma lem7009617 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) (h1 : term24 _128971) : term434 _128971 _93494 _93493.
Proof. exact (EQ_MP (@lem7009616 _128971 _93494 _93493) (@lem7009478 _128971 _93494 _93493 h1)). Qed.
Lemma lem7009639 {_128971 : Type'} (u : _128971 -> Prop) (h1 : term101 _128971 u) : term101 _128971 u.
Proof. exact (h1). Qed.
Lemma lem7009665 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7009701 {_128971 : Type'} (v : _128971 -> Prop) (h1 : term101 _128971 v) : term101 _128971 v.
Proof. exact (h1). Qed.
Lemma lem7009729 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7009751 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93525 : _128971) (_93524 : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term410 _128971 _93523 _93525 _93524.
Proof. exact (EQ_MP (@lem7009570 _128971 _93523 _93525 _93524) (@lem7009569 _128971 _93523 _93524 _93525 x h1)). Qed.
Lemma lem7009771 {_128971 : Type'} (_93530 : _128971 -> Prop) (_93531 : _128971) (_93529 : _128971 -> Prop) (h1 : term22 _128971) : term435 _128971 _93530 _93531 _93529.
Proof. exact (proj1 (@lem7009589 _128971 _93529 _93531 _93530 h1)). Qed.
Lemma lem7009777 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93531 : _128971) (_93530 : _128971 -> Prop) (h1 : term22 _128971) : term436 _128971 _93529 _93531 _93530.
Proof. exact (proj2 (@lem7009589 _128971 _93529 _93531 _93530 h1)). Qed.
Lemma lem7009791 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7009792 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : term437 _128971 v.
Proof. exact (fun h0 : term101 _128971 v => @lem7009791 _128971 v h1). Qed.
Lemma lem7009794 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7009795 {_128971 : Type'} (v : _128971 -> Prop) : (term437 _128971 v) = (@FINITE _128971 v).
Proof. exact (@lem7009794 (@FINITE _128971 v)). Qed.
Lemma lem7009796 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (EQ_MP (@lem7009795 _128971 v) (@lem7009792 _128971 v h1)). Qed.
Lemma lem7009798 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7009799 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : term439 _128971 u v.
Proof. exact (fun h0 : term403 _128971 u v => @lem7009798 _128971 u v h1). Qed.
Lemma lem7009801 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7009802 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : (term439 _128971 u v) = (@SUBSET _128971 u v).
Proof. exact (@lem7009801 (@SUBSET _128971 u v)). Qed.
Lemma lem7009803 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (EQ_MP (@lem7009802 _128971 u v) (@lem7009799 _128971 u v h1)). Qed.
Lemma lem7009819 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7009820 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term440 _128971 _93494 _93493) = (term441 _128971 _93493 _93494).
Proof. exact (@lem7009819 (@FINITE _128971 _93493) (term403 _128971 _93493 _93494)). Qed.
Lemma lem7009826 {_128971 : Type'} (_93494 : _128971 -> Prop) : (term91 _128971 _93494) = (term91 _128971 _93494).
Proof. exact (eq_refl (term91 _128971 _93494)). Qed.
Lemma lem7009827 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term434 _128971 _93494 _93493) = (term442 _128971 _93493 _93494).
Proof. exact (MK_COMB (@lem7009826 _128971 _93494) (@lem7009820 _128971 _93493 _93494)). Qed.
Lemma lem7009831 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7009832 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term442 _128971 _93493 _93494) = (term443 _128971 _93493 _93494).
Proof. exact (@lem7009831 (@FINITE _128971 _93493) (term101 _128971 _93494) (term403 _128971 _93493 _93494)). Qed.
Lemma lem7009848 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term434 _128971 _93494 _93493) = (term443 _128971 _93493 _93494).
Proof. exact (TRANS (@lem7009827 _128971 _93493 _93494) (@lem7009832 _128971 _93493 _93494)). Qed.
Lemma lem7009849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7009850 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term444 _128971 _93494 _93493) = (term445 _128971 _93493 _93494).
Proof. exact (MK_COMB (@lem7009849) (@lem7009848 _128971 _93493 _93494)). Qed.
Lemma lem7009866 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term443 _128971 _93493 _93494) = (term443 _128971 _93493 _93494).
Proof. exact (eq_refl (term443 _128971 _93493 _93494)). Qed.
Lemma lem7009867 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : ((term434 _128971 _93494 _93493) = (term443 _128971 _93493 _93494)) = ((term443 _128971 _93493 _93494) = (term443 _128971 _93493 _93494)).
Proof. exact (MK_COMB (@lem7009850 _128971 _93493 _93494) (@lem7009866 _128971 _93493 _93494)). Qed.
Lemma lem7009869 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7009870 (x : Prop) : (x = x) = True.
Proof. exact (@lem7009869 Prop x). Qed.
Lemma lem7009871 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : ((term443 _128971 _93493 _93494) = (term443 _128971 _93493 _93494)) = True.
Proof. exact (@lem7009870 (term443 _128971 _93493 _93494)). Qed.
Lemma lem7009872 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : ((term434 _128971 _93494 _93493) = (term443 _128971 _93493 _93494)) = True.
Proof. exact (TRANS (@lem7009867 _128971 _93493 _93494) (@lem7009871 _128971 _93493 _93494)). Qed.
Lemma lem7009873 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : True = ((term434 _128971 _93494 _93493) = (term443 _128971 _93493 _93494)).
Proof. exact (SYM (@lem7009872 _128971 _93493 _93494)). Qed.
Lemma lem7009874 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term434 _128971 _93494 _93493) = (term443 _128971 _93493 _93494).
Proof. exact (EQ_MP (@lem7009873 _128971 _93493 _93494) (@lem0)). Qed.
Lemma lem7009875 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) (h1 : term24 _128971) : term443 _128971 _93493 _93494.
Proof. exact (EQ_MP (@lem7009874 _128971 _93493 _93494) (@lem7009617 _128971 _93494 _93493 h1)). Qed.
Lemma lem7009877 (b : Prop) (a : Prop) : (a \/ b) = (term446 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7009878 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) : (term443 _128971 _93493 _93494) = (term447 _128971 _93494 _93493).
Proof. exact (@lem7009877 (term126 _128971 _93493 _93494) (@FINITE _128971 _93493)). Qed.
Lemma lem7009880 (a : Prop) (b : Prop) : (term448 a b) = (term449 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7009881 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term450 _128971 _93493 _93494) = (term451 _128971 _93493 _93494).
Proof. exact (@lem7009880 (term101 _128971 _93494) (term403 _128971 _93493 _93494)). Qed.
Lemma lem7009883 (a : Prop) : (term452 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7009884 {_128971 : Type'} (_93494 : _128971 -> Prop) : (term453 _128971 _93494) = (@FINITE _128971 _93494).
Proof. exact (@lem7009883 (@FINITE _128971 _93494)). Qed.
Lemma lem7009885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7009886 {_128971 : Type'} (_93494 : _128971 -> Prop) : (term454 _128971 _93494) = (term78 _128971 _93494).
Proof. exact (MK_COMB (@lem7009885) (@lem7009884 _128971 _93494)). Qed.
Lemma lem7009888 (a : Prop) : (term452 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7009889 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term455 _128971 _93493 _93494) = (@SUBSET _128971 _93493 _93494).
Proof. exact (@lem7009888 (@SUBSET _128971 _93493 _93494)). Qed.
Lemma lem7009890 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term451 _128971 _93493 _93494) = (term18 _128971 _93493 _93494).
Proof. exact (MK_COMB (@lem7009886 _128971 _93494) (@lem7009889 _128971 _93493 _93494)). Qed.
Lemma lem7009891 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term450 _128971 _93493 _93494) = (term18 _128971 _93493 _93494).
Proof. exact (TRANS (@lem7009881 _128971 _93493 _93494) (@lem7009890 _128971 _93493 _93494)). Qed.
Lemma lem7009892 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7009893 {_128971 : Type'} (_93493 : _128971 -> Prop) (_93494 : _128971 -> Prop) : (term456 _128971 _93493 _93494) = (term457 _128971 _93493 _93494).
Proof. exact (MK_COMB (@lem7009892) (@lem7009891 _128971 _93493 _93494)). Qed.
Lemma lem7009894 {_128971 : Type'} (_93493 : _128971 -> Prop) : (@FINITE _128971 _93493) = (@FINITE _128971 _93493).
Proof. exact (eq_refl (@FINITE _128971 _93493)). Qed.
Lemma lem7009895 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) : (term447 _128971 _93494 _93493) = (term71 _128971 _93494 _93493).
Proof. exact (MK_COMB (@lem7009893 _128971 _93493 _93494) (@lem7009894 _128971 _93493)). Qed.
Lemma lem7009896 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) : (term443 _128971 _93493 _93494) = (term71 _128971 _93494 _93493).
Proof. exact (TRANS (@lem7009878 _128971 _93494 _93493) (@lem7009895 _128971 _93494 _93493)). Qed.
Lemma lem7009898 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : term18 _128971 u v.
Proof. exact (conj (@lem7009796 _128971 v h1) (@lem7009803 _128971 u v h2)). Qed.
Lemma lem7009900 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) (h1 : term24 _128971) : term71 _128971 _93494 _93493.
Proof. exact (EQ_MP (@lem7009896 _128971 _93494 _93493) (@lem7009875 _128971 _93493 _93494 h1)). Qed.
Lemma lem7009901 {_128971 : Type'} (_93494 : _128971 -> Prop) (_93493 : _128971 -> Prop) (h1 : term24 _128971) : term71 _128971 _93494 _93493.
Proof. exact (@lem7009900 _128971 _93494 _93493 h1). Qed.
Lemma lem7009902 {_128971 : Type'} (v : _128971 -> Prop) (u : _128971 -> Prop) (h1 : term24 _128971) : term71 _128971 v u.
Proof. exact (@lem7009901 _128971 v u h1). Qed.
Lemma lem7009905 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : @SUBSET _128971 u v) : @FINITE _128971 u.
Proof. exact (@lem7009902 _128971 v u h1 (@lem7009898 _128971 u v h2 h3)). Qed.
Lemma lem7009906 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : @SUBSET _128971 u v) : term437 _128971 u.
Proof. exact (fun h0 : term101 _128971 u => @lem7009905 _128971 u v h1 h2 h3). Qed.
Lemma lem7009908 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7009909 {_128971 : Type'} (u : _128971 -> Prop) : (term437 _128971 u) = (@FINITE _128971 u).
Proof. exact (@lem7009908 (@FINITE _128971 u)). Qed.
Lemma lem7009910 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : @SUBSET _128971 u v) : @FINITE _128971 u.
Proof. exact (EQ_MP (@lem7009909 _128971 u) (@lem7009906 _128971 u v h1 h2 h3)). Qed.
Lemma lem7009913 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7009915 {_128971 : Type'} (u : _128971 -> Prop) : (term101 _128971 u) = (term458 _128971 u).
Proof. exact (@lem7009913 (@FINITE _128971 u)). Qed.
Lemma lem7009918 {_128971 : Type'} (u : _128971 -> Prop) (h1 : term101 _128971 u) : term458 _128971 u.
Proof. exact (EQ_MP (@lem7009915 _128971 u) (@lem7009639 _128971 u h1)). Qed.
Lemma lem7009921 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (@lem7009918 _128971 u h3 (@lem7009910 _128971 u v h1 h2 h4)). Qed.
Lemma lem7009922 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : term459.
Proof. exact (fun h0 : ~ False => @lem7009921 _128971 u v h1 h2 h3 h4). Qed.
Lemma lem7009924 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7009925 : term459 = False.
Proof. exact (@lem7009924 False). Qed.
Lemma lem7009926 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7009925) (@lem7009922 _128971 u v h1 h2 h3 h4)). Qed.
Lemma lem7009928 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (h1). Qed.
Lemma lem7009929 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : term437 _128971 v.
Proof. exact (fun h0 : term101 _128971 v => @lem7009928 _128971 v h1). Qed.
Lemma lem7009931 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7009932 {_128971 : Type'} (v : _128971 -> Prop) : (term437 _128971 v) = (@FINITE _128971 v).
Proof. exact (@lem7009931 (@FINITE _128971 v)). Qed.
Lemma lem7009933 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : @FINITE _128971 v.
Proof. exact (EQ_MP (@lem7009932 _128971 v) (@lem7009929 _128971 v h1)). Qed.
Lemma lem7009936 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7009938 {_128971 : Type'} (v : _128971 -> Prop) : (term101 _128971 v) = (term458 _128971 v).
Proof. exact (@lem7009936 (@FINITE _128971 v)). Qed.
Lemma lem7009941 {_128971 : Type'} (v : _128971 -> Prop) (h1 : term101 _128971 v) : term458 _128971 v.
Proof. exact (EQ_MP (@lem7009938 _128971 v) (@lem7009701 _128971 v h1)). Qed.
Lemma lem7009944 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : False.
Proof. exact (@lem7009941 _128971 v h2 (@lem7009933 _128971 v h1)). Qed.
Lemma lem7009945 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : term459.
Proof. exact (fun h0 : ~ False => @lem7009944 _128971 v h1 h2). Qed.
Lemma lem7009947 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7009948 : term459 = False.
Proof. exact (@lem7009947 False). Qed.
Lemma lem7009949 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : False.
Proof. exact (EQ_MP (@lem7009948) (@lem7009945 _128971 v h1 h2)). Qed.
Lemma lem7010053 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term81 _128971 u v f x') : term57 _128971 x' u v.
Proof. exact (proj1 (@lem7008896 _128971 u v f x' h1)). Qed.
Lemma lem7010054 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term81 _128971 u v f x') : term460 _128971 x' u v.
Proof. exact (fun h0 : term419 _128971 x' u v => @lem7010053 _128971 u v f x' h1). Qed.
Lemma lem7010056 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7010057 {_128971 : Type'} (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) : (term460 _128971 x' u v) = (term57 _128971 x' u v).
Proof. exact (@lem7010056 (term57 _128971 x' u v)). Qed.
Lemma lem7010058 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term81 _128971 u v f x') : term57 _128971 x' u v.
Proof. exact (EQ_MP (@lem7010057 _128971 x' u v) (@lem7010054 _128971 u v f x' h1)). Qed.
Lemma lem7010060 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7010061 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : term439 _128971 u v.
Proof. exact (fun h0 : term403 _128971 u v => @lem7010060 _128971 u v h1). Qed.
Lemma lem7010063 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7010064 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : (term439 _128971 u v) = (@SUBSET _128971 u v).
Proof. exact (@lem7010063 (@SUBSET _128971 u v)). Qed.
Lemma lem7010065 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @SUBSET _128971 u v) : @SUBSET _128971 u v.
Proof. exact (EQ_MP (@lem7010064 _128971 u v) (@lem7010061 _128971 u v h1)). Qed.
Lemma lem7010067 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term81 _128971 u v f x') : term57 _128971 x' u v.
Proof. exact (proj1 (@lem7008896 _128971 u v f x' h1)). Qed.
Lemma lem7010068 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term81 _128971 u v f x') : term460 _128971 x' u v.
Proof. exact (fun h0 : term419 _128971 x' u v => @lem7010067 _128971 u v f x' h1). Qed.
Lemma lem7010070 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7010071 {_128971 : Type'} (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) : (term460 _128971 x' u v) = (term57 _128971 x' u v).
Proof. exact (@lem7010070 (term57 _128971 x' u v)). Qed.
Lemma lem7010072 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term81 _128971 u v f x') : term57 _128971 x' u v.
Proof. exact (EQ_MP (@lem7010071 _128971 x' u v) (@lem7010068 _128971 u v f x' h1)). Qed.
Lemma lem7010078 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7010079 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : (term435 _128971 _93530 _93531 _93529) = (term461 _128971 _93531 _93529 _93530).
Proof. exact (@lem7010078 (@IN _128971 _93531 _93529) (term419 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7010086 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : (term462 _128971 _93530 _93531 _93529) = (term463 _128971 _93531 _93529 _93530).
Proof. exact (MK_COMB (@lem7010085) (@lem7010079 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010092 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : (term461 _128971 _93531 _93529 _93530) = (term461 _128971 _93531 _93529 _93530).
Proof. exact (eq_refl (term461 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010093 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : ((term435 _128971 _93530 _93531 _93529) = (term461 _128971 _93531 _93529 _93530)) = ((term461 _128971 _93531 _93529 _93530) = (term461 _128971 _93531 _93529 _93530)).
Proof. exact (MK_COMB (@lem7010086 _128971 _93531 _93529 _93530) (@lem7010092 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010095 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7010096 (x : Prop) : (x = x) = True.
Proof. exact (@lem7010095 Prop x). Qed.
Lemma lem7010097 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : ((term461 _128971 _93531 _93529 _93530) = (term461 _128971 _93531 _93529 _93530)) = True.
Proof. exact (@lem7010096 (term461 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010098 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : ((term435 _128971 _93530 _93531 _93529) = (term461 _128971 _93531 _93529 _93530)) = True.
Proof. exact (TRANS (@lem7010093 _128971 _93531 _93529 _93530) (@lem7010097 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010099 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : True = ((term435 _128971 _93530 _93531 _93529) = (term461 _128971 _93531 _93529 _93530)).
Proof. exact (SYM (@lem7010098 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010100 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : (term435 _128971 _93530 _93531 _93529) = (term461 _128971 _93531 _93529 _93530).
Proof. exact (EQ_MP (@lem7010099 _128971 _93531 _93529 _93530) (@lem0)). Qed.
Lemma lem7010101 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) (h1 : term22 _128971) : term461 _128971 _93531 _93529 _93530.
Proof. exact (EQ_MP (@lem7010100 _128971 _93531 _93529 _93530) (@lem7009771 _128971 _93530 _93531 _93529 h1)). Qed.
Lemma lem7010103 (b : Prop) (a : Prop) : (a \/ b) = (term446 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7010104 {_128971 : Type'} (_93530 : _128971 -> Prop) (_93531 : _128971) (_93529 : _128971 -> Prop) : (term461 _128971 _93531 _93529 _93530) = (term464 _128971 _93530 _93531 _93529).
Proof. exact (@lem7010103 (term419 _128971 _93531 _93529 _93530) (@IN _128971 _93531 _93529)). Qed.
Lemma lem7010106 (a : Prop) : (term452 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7010107 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : (term465 _128971 _93531 _93529 _93530) = (term57 _128971 _93531 _93529 _93530).
Proof. exact (@lem7010106 (term57 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010108 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7010109 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) (_93530 : _128971 -> Prop) : (term466 _128971 _93531 _93529 _93530) = (term467 _128971 _93531 _93529 _93530).
Proof. exact (MK_COMB (@lem7010108) (@lem7010107 _128971 _93531 _93529 _93530)). Qed.
Lemma lem7010110 {_128971 : Type'} (_93531 : _128971) (_93529 : _128971 -> Prop) : (@IN _128971 _93531 _93529) = (@IN _128971 _93531 _93529).
Proof. exact (eq_refl (@IN _128971 _93531 _93529)). Qed.
Lemma lem7010111 {_128971 : Type'} (_93530 : _128971 -> Prop) (_93531 : _128971) (_93529 : _128971 -> Prop) : (term464 _128971 _93530 _93531 _93529) = (term468 _128971 _93530 _93531 _93529).
Proof. exact (MK_COMB (@lem7010109 _128971 _93531 _93529 _93530) (@lem7010110 _128971 _93531 _93529)). Qed.
Lemma lem7010112 {_128971 : Type'} (_93530 : _128971 -> Prop) (_93531 : _128971) (_93529 : _128971 -> Prop) : (term461 _128971 _93531 _93529 _93530) = (term468 _128971 _93530 _93531 _93529).
Proof. exact (TRANS (@lem7010104 _128971 _93530 _93531 _93529) (@lem7010111 _128971 _93530 _93531 _93529)). Qed.
Lemma lem7010115 {_128971 : Type'} (_93530 : _128971 -> Prop) (_93531 : _128971) (_93529 : _128971 -> Prop) (h1 : term22 _128971) : term468 _128971 _93530 _93531 _93529.
Proof. exact (EQ_MP (@lem7010112 _128971 _93530 _93531 _93529) (@lem7010101 _128971 _93531 _93529 _93530 h1)). Qed.
Lemma lem7010116 {_128971 : Type'} (_93530 : _128971 -> Prop) (_93531 : _128971) (_93529 : _128971 -> Prop) (h1 : term22 _128971) : term468 _128971 _93530 _93531 _93529.
Proof. exact (@lem7010115 _128971 _93530 _93531 _93529 h1). Qed.
Lemma lem7010117 {_128971 : Type'} (v : _128971 -> Prop) (x' : _128971) (u : _128971 -> Prop) (h1 : term22 _128971) : term468 _128971 v x' u.
Proof. exact (@lem7010116 _128971 v x' u h1). Qed.
Lemma lem7010120 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term81 _128971 u v f x') : @IN _128971 x' u.
Proof. exact (@lem7010117 _128971 v x' u h1 (@lem7010072 _128971 u v f x' h2)). Qed.
Lemma lem7010121 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term81 _128971 u v f x') : term469 _128971 x' u.
Proof. exact (fun h0 : term316 _128971 x' u => @lem7010120 _128971 u v f x' h1 h2). Qed.
Lemma lem7010123 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7010124 {_128971 : Type'} (x' : _128971) (u : _128971 -> Prop) : (term469 _128971 x' u) = (@IN _128971 x' u).
Proof. exact (@lem7010123 (@IN _128971 x' u)). Qed.
Lemma lem7010125 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term81 _128971 u v f x') : @IN _128971 x' u.
Proof. exact (EQ_MP (@lem7010124 _128971 x' u) (@lem7010121 _128971 u v f x' h1 h2)). Qed.
Lemma lem7010131 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7010132 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93525 : _128971) (_93524 : _128971 -> Prop) : (term410 _128971 _93523 _93525 _93524) = (term470 _128971 _93523 _93525 _93524).
Proof. exact (@lem7010131 (term316 _128971 _93525 _93523) (term403 _128971 _93523 _93524) (@IN _128971 _93525 _93524)). Qed.
Lemma lem7010146 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7010147 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term471 _128971 _93523 _93525 _93524) = (term472 _128971 _93525 _93523 _93524).
Proof. exact (@lem7010146 (@IN _128971 _93525 _93524) (term403 _128971 _93523 _93524)). Qed.
Lemma lem7010153 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) : (term313 _128971 _93525 _93523) = (term313 _128971 _93525 _93523).
Proof. exact (eq_refl (term313 _128971 _93525 _93523)). Qed.
Lemma lem7010154 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term470 _128971 _93523 _93525 _93524) = (term473 _128971 _93525 _93523 _93524).
Proof. exact (MK_COMB (@lem7010153 _128971 _93525 _93523) (@lem7010147 _128971 _93525 _93523 _93524)). Qed.
Lemma lem7010158 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7010159 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term473 _128971 _93525 _93523 _93524) = (term474 _128971 _93525 _93523 _93524).
Proof. exact (@lem7010158 (@IN _128971 _93525 _93524) (term316 _128971 _93525 _93523) (term403 _128971 _93523 _93524)). Qed.
Lemma lem7010175 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term470 _128971 _93523 _93525 _93524) = (term474 _128971 _93525 _93523 _93524).
Proof. exact (TRANS (@lem7010154 _128971 _93525 _93523 _93524) (@lem7010159 _128971 _93525 _93523 _93524)). Qed.
Lemma lem7010176 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term410 _128971 _93523 _93525 _93524) = (term474 _128971 _93525 _93523 _93524).
Proof. exact (TRANS (@lem7010132 _128971 _93523 _93525 _93524) (@lem7010175 _128971 _93525 _93523 _93524)). Qed.
Lemma lem7010177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7010178 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term475 _128971 _93523 _93525 _93524) = (term476 _128971 _93525 _93523 _93524).
Proof. exact (MK_COMB (@lem7010177) (@lem7010176 _128971 _93525 _93523 _93524)). Qed.
Lemma lem7010192 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7010193 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term477 _128971 _93524 _93525 _93523) = (term478 _128971 _93525 _93523 _93524).
Proof. exact (@lem7010192 (term316 _128971 _93525 _93523) (term403 _128971 _93523 _93524)). Qed.
Lemma lem7010199 {_128971 : Type'} (_93525 : _128971) (_93524 : _128971 -> Prop) : (term479 _128971 _93525 _93524) = (term479 _128971 _93525 _93524).
Proof. exact (eq_refl (term479 _128971 _93525 _93524)). Qed.
Lemma lem7010200 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term480 _128971 _93524 _93525 _93523) = (term474 _128971 _93525 _93523 _93524).
Proof. exact (MK_COMB (@lem7010199 _128971 _93525 _93524) (@lem7010193 _128971 _93525 _93523 _93524)). Qed.
Lemma lem7010211 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : ((term410 _128971 _93523 _93525 _93524) = (term480 _128971 _93524 _93525 _93523)) = ((term474 _128971 _93525 _93523 _93524) = (term474 _128971 _93525 _93523 _93524)).
Proof. exact (MK_COMB (@lem7010178 _128971 _93525 _93523 _93524) (@lem7010200 _128971 _93525 _93523 _93524)). Qed.
Lemma lem7010213 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7010214 (x : Prop) : (x = x) = True.
Proof. exact (@lem7010213 Prop x). Qed.
Lemma lem7010215 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : ((term474 _128971 _93525 _93523 _93524) = (term474 _128971 _93525 _93523 _93524)) = True.
Proof. exact (@lem7010214 (term474 _128971 _93525 _93523 _93524)). Qed.
Lemma lem7010216 {_128971 : Type'} (_93524 : _128971 -> Prop) (_93525 : _128971) (_93523 : _128971 -> Prop) : ((term410 _128971 _93523 _93525 _93524) = (term480 _128971 _93524 _93525 _93523)) = True.
Proof. exact (TRANS (@lem7010211 _128971 _93525 _93523 _93524) (@lem7010215 _128971 _93525 _93523 _93524)). Qed.
Lemma lem7010217 {_128971 : Type'} (_93524 : _128971 -> Prop) (_93525 : _128971) (_93523 : _128971 -> Prop) : True = ((term410 _128971 _93523 _93525 _93524) = (term480 _128971 _93524 _93525 _93523)).
Proof. exact (SYM (@lem7010216 _128971 _93524 _93525 _93523)). Qed.
Lemma lem7010218 {_128971 : Type'} (_93524 : _128971 -> Prop) (_93525 : _128971) (_93523 : _128971 -> Prop) : (term410 _128971 _93523 _93525 _93524) = (term480 _128971 _93524 _93525 _93523).
Proof. exact (EQ_MP (@lem7010217 _128971 _93524 _93525 _93523) (@lem0)). Qed.
Lemma lem7010219 {_128971 : Type'} (_93524 : _128971 -> Prop) (_93525 : _128971) (_93523 : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term480 _128971 _93524 _93525 _93523.
Proof. exact (EQ_MP (@lem7010218 _128971 _93524 _93525 _93523) (@lem7009751 _128971 _93523 _93525 _93524 x h1)). Qed.
Lemma lem7010221 (b : Prop) (a : Prop) : (a \/ b) = (term446 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7010222 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93525 : _128971) (_93524 : _128971 -> Prop) : (term480 _128971 _93524 _93525 _93523) = (term481 _128971 _93523 _93525 _93524).
Proof. exact (@lem7010221 (term477 _128971 _93524 _93525 _93523) (@IN _128971 _93525 _93524)). Qed.
Lemma lem7010224 (a : Prop) (b : Prop) : (term448 a b) = (term449 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7010225 {_128971 : Type'} (_93524 : _128971 -> Prop) (_93525 : _128971) (_93523 : _128971 -> Prop) : (term482 _128971 _93524 _93525 _93523) = (term483 _128971 _93524 _93525 _93523).
Proof. exact (@lem7010224 (term403 _128971 _93523 _93524) (term316 _128971 _93525 _93523)). Qed.
Lemma lem7010227 (a : Prop) : (term452 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7010228 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term455 _128971 _93523 _93524) = (@SUBSET _128971 _93523 _93524).
Proof. exact (@lem7010227 (@SUBSET _128971 _93523 _93524)). Qed.
Lemma lem7010229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7010230 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93524 : _128971 -> Prop) : (term484 _128971 _93523 _93524) = (term485 _128971 _93523 _93524).
Proof. exact (MK_COMB (@lem7010229) (@lem7010228 _128971 _93523 _93524)). Qed.
Lemma lem7010232 (a : Prop) : (term452 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7010233 {_128971 : Type'} (_93525 : _128971) (_93523 : _128971 -> Prop) : (term312 _128971 _93525 _93523) = (@IN _128971 _93525 _93523).
Proof. exact (@lem7010232 (@IN _128971 _93525 _93523)). Qed.
Lemma lem7010234 {_128971 : Type'} (_93524 : _128971 -> Prop) (_93525 : _128971) (_93523 : _128971 -> Prop) : (term483 _128971 _93524 _93525 _93523) = (term486 _128971 _93524 _93525 _93523).
Proof. exact (MK_COMB (@lem7010230 _128971 _93523 _93524) (@lem7010233 _128971 _93525 _93523)). Qed.
Lemma lem7010235 {_128971 : Type'} (_93524 : _128971 -> Prop) (_93525 : _128971) (_93523 : _128971 -> Prop) : (term482 _128971 _93524 _93525 _93523) = (term486 _128971 _93524 _93525 _93523).
Proof. exact (TRANS (@lem7010225 _128971 _93524 _93525 _93523) (@lem7010234 _128971 _93524 _93525 _93523)). Qed.
Lemma lem7010236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7010237 {_128971 : Type'} (_93524 : _128971 -> Prop) (_93525 : _128971) (_93523 : _128971 -> Prop) : (term487 _128971 _93524 _93525 _93523) = (term488 _128971 _93524 _93525 _93523).
Proof. exact (MK_COMB (@lem7010236) (@lem7010235 _128971 _93524 _93525 _93523)). Qed.
Lemma lem7010238 {_128971 : Type'} (_93525 : _128971) (_93524 : _128971 -> Prop) : (@IN _128971 _93525 _93524) = (@IN _128971 _93525 _93524).
Proof. exact (eq_refl (@IN _128971 _93525 _93524)). Qed.
Lemma lem7010239 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93525 : _128971) (_93524 : _128971 -> Prop) : (term481 _128971 _93523 _93525 _93524) = (term489 _128971 _93523 _93525 _93524).
Proof. exact (MK_COMB (@lem7010237 _128971 _93524 _93525 _93523) (@lem7010238 _128971 _93525 _93524)). Qed.
Lemma lem7010240 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93525 : _128971) (_93524 : _128971 -> Prop) : (term480 _128971 _93524 _93525 _93523) = (term489 _128971 _93523 _93525 _93524).
Proof. exact (TRANS (@lem7010222 _128971 _93523 _93525 _93524) (@lem7010239 _128971 _93523 _93525 _93524)). Qed.
Lemma lem7010242 {_128971 : Type'} (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term81 _128971 u v f x') (h3 : @SUBSET _128971 u v) : term486 _128971 v x' u.
Proof. exact (conj (@lem7010065 _128971 u v h3) (@lem7010125 _128971 u v f x' h1 h2)). Qed.
Lemma lem7010244 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93525 : _128971) (_93524 : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term489 _128971 _93523 _93525 _93524.
Proof. exact (EQ_MP (@lem7010240 _128971 _93523 _93525 _93524) (@lem7010219 _128971 _93524 _93525 _93523 x h1)). Qed.
Lemma lem7010245 {_128971 : Type'} (_93523 : _128971 -> Prop) (_93525 : _128971) (_93524 : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term489 _128971 _93523 _93525 _93524.
Proof. exact (@lem7010244 _128971 _93523 _93525 _93524 x h1). Qed.
Lemma lem7010246 {_128971 : Type'} (u : _128971 -> Prop) (x' : _128971) (v : _128971 -> Prop) (x : type638 _128971) (h1 : term308 _128971 x) : term489 _128971 u x' v.
Proof. exact (@lem7010245 _128971 u x' v x h1). Qed.
Lemma lem7010249 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : @IN _128971 x' v.
Proof. exact (@lem7010246 _128971 u x' v x h2 (@lem7010242 _128971 f x' u v h1 h3 h4)). Qed.
Lemma lem7010250 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : term469 _128971 x' v.
Proof. exact (fun h0 : term316 _128971 x' v => @lem7010249 _128971 x f x' u v h1 h2 h3 h4). Qed.
Lemma lem7010252 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7010253 {_128971 : Type'} (x' : _128971) (v : _128971 -> Prop) : (term469 _128971 x' v) = (@IN _128971 x' v).
Proof. exact (@lem7010252 (@IN _128971 x' v)). Qed.
Lemma lem7010254 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : @IN _128971 x' v.
Proof. exact (EQ_MP (@lem7010253 _128971 x' v) (@lem7010250 _128971 x f x' u v h1 h2 h3 h4)). Qed.
Lemma lem7010256 (a : Prop) (b : Prop) : (term490 a b) = (term491 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7010257 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93531 : _128971) (_93530 : _128971 -> Prop) : (term436 _128971 _93529 _93531 _93530) = (term492 _128971 _93529 _93531 _93530).
Proof. exact (@lem7010256 (term57 _128971 _93531 _93529 _93530) (@IN _128971 _93531 _93530)). Qed.
Lemma lem7010259 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7010260 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93531 : _128971) (_93530 : _128971 -> Prop) : (term492 _128971 _93529 _93531 _93530) = (term493 _128971 _93529 _93531 _93530).
Proof. exact (@lem7010259 (term494 _128971 _93529 _93531 _93530)). Qed.
Lemma lem7010261 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93531 : _128971) (_93530 : _128971 -> Prop) : (term436 _128971 _93529 _93531 _93530) = (term493 _128971 _93529 _93531 _93530).
Proof. exact (TRANS (@lem7010257 _128971 _93529 _93531 _93530) (@lem7010260 _128971 _93529 _93531 _93530)). Qed.
Lemma lem7010263 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : term494 _128971 u x' v.
Proof. exact (conj (@lem7010058 _128971 u v f x' h3) (@lem7010254 _128971 x f x' u v h1 h2 h3 h4)). Qed.
Lemma lem7010265 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93531 : _128971) (_93530 : _128971 -> Prop) (h1 : term22 _128971) : term493 _128971 _93529 _93531 _93530.
Proof. exact (EQ_MP (@lem7010261 _128971 _93529 _93531 _93530) (@lem7009777 _128971 _93529 _93531 _93530 h1)). Qed.
Lemma lem7010266 {_128971 : Type'} (_93529 : _128971 -> Prop) (_93531 : _128971) (_93530 : _128971 -> Prop) (h1 : term22 _128971) : term493 _128971 _93529 _93531 _93530.
Proof. exact (@lem7010265 _128971 _93529 _93531 _93530 h1). Qed.
Lemma lem7010267 {_128971 : Type'} (u : _128971 -> Prop) (x' : _128971) (v : _128971 -> Prop) (h1 : term22 _128971) : term493 _128971 u x' v.
Proof. exact (@lem7010266 _128971 u x' v h1). Qed.
Lemma lem7010270 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : False.
Proof. exact (@lem7010267 _128971 u x' v h1 (@lem7010263 _128971 x f x' u v h1 h2 h3 h4)). Qed.
Lemma lem7010271 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : term459.
Proof. exact (fun h0 : ~ False => @lem7010270 _128971 x f x' u v h1 h2 h3 h4). Qed.
Lemma lem7010273 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7010274 : term459 = False.
Proof. exact (@lem7010273 False). Qed.
Lemma lem7010275 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010274) (@lem7010271 _128971 x f x' u v h1 h2 h3 h4)). Qed.
Lemma lem7010276 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : (@SUBSET _128971 u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET _128971 u v => @lem7010275 _128971 x f x' u v h1 h2 h3 h4) (fun h5 : False => @lem7009729 _128971 u v h4)). Qed.
Lemma lem7010277 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010276 _128971 x f x' u v h1 h2 h3 h4) (@lem7009729 _128971 u v h4)). Qed.
Lemma lem7010278 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : (term101 _128971 v) = False.
Proof. exact (prop_ext (fun h3 : term101 _128971 v => @lem7009949 _128971 v h1 h2) (fun h3 : False => @lem7009701 _128971 v h2)). Qed.
Lemma lem7010279 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : False.
Proof. exact (EQ_MP (@lem7010278 _128971 v h1 h2) (@lem7009701 _128971 v h2)). Qed.
Lemma lem7010280 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : (@FINITE _128971 v) = False.
Proof. exact (prop_ext (fun h3 : @FINITE _128971 v => @lem7010279 _128971 v h1 h2) (fun h3 : False => @lem7009665 _128971 v h1)). Qed.
Lemma lem7010281 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : False.
Proof. exact (EQ_MP (@lem7010280 _128971 v h1 h2) (@lem7009665 _128971 v h1)). Qed.
Lemma lem7010282 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (term101 _128971 u) = False.
Proof. exact (prop_ext (fun h5 : term101 _128971 u => @lem7009926 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7009639 _128971 u h3)). Qed.
Lemma lem7010283 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010282 _128971 u v h1 h2 h3 h4) (@lem7009639 _128971 u h3)). Qed.
Lemma lem7010284 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (@SUBSET _128971 u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET _128971 u v => @lem7010283 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7009605 _128971 u v h4)). Qed.
Lemma lem7010285 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010284 _128971 u v h1 h2 h3 h4) (@lem7009605 _128971 u v h4)). Qed.
Lemma lem7010286 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (@FINITE _128971 v) = False.
Proof. exact (prop_ext (fun h5 : @FINITE _128971 v => @lem7010285 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7009603 _128971 v h2)). Qed.
Lemma lem7010287 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010286 _128971 u v h1 h2 h3 h4) (@lem7009603 _128971 v h2)). Qed.
Lemma lem7010288 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : (@SUBSET _128971 u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET _128971 u v => @lem7010277 _128971 x f x' u v h1 h2 h3 h4) (fun h5 : False => @lem7009286 _128971 u v h4)). Qed.
Lemma lem7010289 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010288 _128971 x f x' u v h1 h2 h3 h4) (@lem7009286 _128971 u v h4)). Qed.
Lemma lem7010290 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : (term101 _128971 v) = False.
Proof. exact (prop_ext (fun h3 : term101 _128971 v => @lem7010281 _128971 v h1 h2) (fun h3 : False => @lem7009278 _128971 v h2)). Qed.
Lemma lem7010291 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : False.
Proof. exact (EQ_MP (@lem7010290 _128971 v h1 h2) (@lem7009278 _128971 v h2)). Qed.
Lemma lem7010292 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : (@FINITE _128971 v) = False.
Proof. exact (prop_ext (fun h3 : @FINITE _128971 v => @lem7010291 _128971 v h1 h2) (fun h3 : False => @lem7009092 _128971 v h1)). Qed.
Lemma lem7010293 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : False.
Proof. exact (EQ_MP (@lem7010292 _128971 v h1 h2) (@lem7009092 _128971 v h1)). Qed.
Lemma lem7010294 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (term101 _128971 u) = False.
Proof. exact (prop_ext (fun h5 : term101 _128971 u => @lem7010287 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7009088 _128971 u h3)). Qed.
Lemma lem7010295 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010294 _128971 u v h1 h2 h3 h4) (@lem7009088 _128971 u h3)). Qed.
Lemma lem7010296 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (@SUBSET _128971 u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET _128971 u v => @lem7010295 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7008906 _128971 u v h4)). Qed.
Lemma lem7010297 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010296 _128971 u v h1 h2 h3 h4) (@lem7008906 _128971 u v h4)). Qed.
Lemma lem7010298 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (@FINITE _128971 v) = False.
Proof. exact (prop_ext (fun h5 : @FINITE _128971 v => @lem7010297 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7008902 _128971 v h2)). Qed.
Lemma lem7010299 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010298 _128971 u v h1 h2 h3 h4) (@lem7008902 _128971 v h2)). Qed.
Lemma lem7010300 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : (@SUBSET _128971 u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET _128971 u v => @lem7010289 _128971 x f x' u v h1 h2 h3 h4) (fun h5 : False => @lem7009286 _128971 u v h4)). Qed.
Lemma lem7010301 {_128971 : Type'} (x : type638 _128971) (f : _128971 -> nat) (x' : _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term308 _128971 x) (h3 : term81 _128971 u v f x') (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010300 _128971 x f x' u v h1 h2 h3 h4) (@lem7009286 _128971 u v h4)). Qed.
Lemma lem7010302 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : (term101 _128971 v) = False.
Proof. exact (prop_ext (fun h3 : term101 _128971 v => @lem7010293 _128971 v h1 h2) (fun h3 : False => @lem7009278 _128971 v h2)). Qed.
Lemma lem7010303 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : False.
Proof. exact (EQ_MP (@lem7010302 _128971 v h1 h2) (@lem7009278 _128971 v h2)). Qed.
Lemma lem7010304 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : (@FINITE _128971 v) = False.
Proof. exact (prop_ext (fun h3 : @FINITE _128971 v => @lem7010303 _128971 v h1 h2) (fun h3 : False => @lem7009092 _128971 v h1)). Qed.
Lemma lem7010305 {_128971 : Type'} (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term101 _128971 v) : False.
Proof. exact (EQ_MP (@lem7010304 _128971 v h1 h2) (@lem7009092 _128971 v h1)). Qed.
Lemma lem7010306 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (term101 _128971 u) = False.
Proof. exact (prop_ext (fun h5 : term101 _128971 u => @lem7010299 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7009088 _128971 u h3)). Qed.
Lemma lem7010307 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010306 _128971 u v h1 h2 h3 h4) (@lem7009088 _128971 u h3)). Qed.
Lemma lem7010308 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (@SUBSET _128971 u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET _128971 u v => @lem7010307 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7008906 _128971 u v h4)). Qed.
Lemma lem7010309 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010308 _128971 u v h1 h2 h3 h4) (@lem7008906 _128971 u v h4)). Qed.
Lemma lem7010310 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : (@FINITE _128971 v) = False.
Proof. exact (prop_ext (fun h5 : @FINITE _128971 v => @lem7010309 _128971 u v h1 h2 h3 h4) (fun h5 : False => @lem7008902 _128971 v h2)). Qed.
Lemma lem7010311 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term101 _128971 u) (h4 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010310 _128971 u v h1 h2 h3 h4) (@lem7008902 _128971 v h2)). Qed.
Lemma lem7010312 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : @FINITE _128971 v) (h3 : term308 _128971 x) (h4 : @SUBSET _128971 u v) (h5 : term108 _128971 u v f x') : False.
Proof. exact (or_elim (@lem7008894 _128971 u v f x' h5) (fun h0 : term101 _128971 v => @lem7010305 _128971 v h2 h0) (fun h0 : term81 _128971 u v f x' => @lem7010301 _128971 x f x' u v h1 h3 h0 h4)). Qed.
Lemma lem7010313 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : False.
Proof. exact (or_elim (@lem7008888 _128971 u v f x' h6) (fun h0 : term101 _128971 u => @lem7010311 _128971 u v h2 h3 h0 h5) (fun h0 : term108 _128971 u v f x' => @lem7010312 _128971 x u v f x' h1 h3 h4 h5 h0)). Qed.
Lemma lem7010314 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : (term121 _128971 u v f x') = False.
Proof. exact (prop_ext (fun h7 : term121 _128971 u v f x' => @lem7010313 _128971 x u v f x' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7008888 _128971 u v f x' h6)). Qed.
Lemma lem7010315 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : False.
Proof. exact (EQ_MP (@lem7010314 _128971 x u v f x' h1 h2 h3 h4 h5 h6) (@lem7008888 _128971 u v f x' h6)). Qed.
Lemma lem7010316 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : (term308 _128971 x) = False.
Proof. exact (prop_ext (fun h7 : term308 _128971 x => @lem7010315 _128971 x u v f x' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7008848 _128971 x h4)). Qed.
Lemma lem7010317 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : False.
Proof. exact (EQ_MP (@lem7010316 _128971 x u v f x' h1 h2 h3 h4 h5 h6) (@lem7008848 _128971 x h4)). Qed.
Lemma lem7010318 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : (@SUBSET _128971 u v) = False.
Proof. exact (prop_ext (fun h7 : @SUBSET _128971 u v => @lem7010317 _128971 x u v f x' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7008667 _128971 u v h5)). Qed.
Lemma lem7010319 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : False.
Proof. exact (EQ_MP (@lem7010318 _128971 x u v f x' h1 h2 h3 h4 h5 h6) (@lem7008667 _128971 u v h5)). Qed.
Lemma lem7010320 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : (@FINITE _128971 v) = False.
Proof. exact (prop_ext (fun h7 : @FINITE _128971 v => @lem7010319 _128971 x u v f x' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7008661 _128971 v h3)). Qed.
Lemma lem7010321 {_128971 : Type'} (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (x' : _128971) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term308 _128971 x) (h5 : @SUBSET _128971 u v) (h6 : term121 _128971 u v f x') : False.
Proof. exact (EQ_MP (@lem7010320 _128971 x u v f x' h1 h2 h3 h4 h5 h6) (@lem7008661 _128971 v h3)). Qed.
Lemma lem7010322 {_128971 : Type'} (f : _128971 -> nat) (x : type638 _128971) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term21 _128971 u v f) (h5 : term308 _128971 x) (h6 : @SUBSET _128971 u v) : False.
Proof. exact (ex_elim (@lem7007432 _128971 u v f h4) (fun x' : _128971 => fun h0 : term123 _128971 u v f x' => @lem7010321 _128971 x u v f x' h1 h2 h3 h5 h6 h0)). Qed.
Lemma lem7010323 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term23 _128971) (h3 : term24 _128971) (h4 : @FINITE _128971 v) (h5 : term21 _128971 u v f) (h6 : @SUBSET _128971 u v) : False.
Proof. exact (ex_elim (@lem7008206 _128971 h2) (fun x : type638 _128971 => fun h0 : term310 _128971 x => @lem7010322 _128971 f x u v h1 h3 h4 h5 h0 h6)). Qed.
Lemma lem7010324 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term23 _128971) (h3 : term24 _128971) (h4 : @FINITE _128971 v) (h5 : term21 _128971 u v f) (h6 : @SUBSET _128971 u v) : (@SUBSET _128971 u v) = False.
Proof. exact (prop_ext (fun h7 : @SUBSET _128971 u v => @lem7010323 _128971 f u v h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7007308 _128971 u v h6)). Qed.
Lemma lem7010325 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term23 _128971) (h3 : term24 _128971) (h4 : @FINITE _128971 v) (h5 : term21 _128971 u v f) (h6 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010324 _128971 f u v h1 h2 h3 h4 h5 h6) (@lem7007308 _128971 u v h6)). Qed.
Lemma lem7010326 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term23 _128971) (h3 : term24 _128971) (h4 : @FINITE _128971 v) (h5 : term21 _128971 u v f) (h6 : @SUBSET _128971 u v) : (@FINITE _128971 v) = False.
Proof. exact (prop_ext (fun h7 : @FINITE _128971 v => @lem7010325 _128971 f u v h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7007302 _128971 v h4)). Qed.
Lemma lem7010327 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term22 _128971) (h2 : term23 _128971) (h3 : term24 _128971) (h4 : @FINITE _128971 v) (h5 : term21 _128971 u v f) (h6 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010326 _128971 f u v h1 h2 h3 h4 h5 h6) (@lem7007302 _128971 v h4)). Qed.
Lemma lem7010328 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term23 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term21 _128971 u v f) (h5 : @SUBSET _128971 u v) : term29 _128971.
Proof. exact (fun h0 : term22 _128971 => @lem7010327 _128971 f u v h0 h1 h2 h3 h4 h5). Qed.
Lemma lem7010329 {_128971 : Type'} : (term29 _128971) = (term30 _128971).
Proof. exact (@lem69 (term22 _128971)). Qed.
Lemma lem7010330 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term23 _128971) (h2 : term24 _128971) (h3 : @FINITE _128971 v) (h4 : term21 _128971 u v f) (h5 : @SUBSET _128971 u v) : term30 _128971.
Proof. exact (EQ_MP (@lem7010329 _128971) (@lem7010328 _128971 f u v h1 h2 h3 h4 h5)). Qed.
Lemma lem7010331 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term24 _128971) (h2 : @FINITE _128971 v) (h3 : term21 _128971 u v f) (h4 : @SUBSET _128971 u v) : term33 _128971.
Proof. exact (fun h0 : term23 _128971 => @lem7010330 _128971 f u v h0 h1 h2 h3 h4). Qed.
Lemma lem7010332 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term21 _128971 u v f) (h3 : @SUBSET _128971 u v) : term36 _128971.
Proof. exact (fun h0 : term24 _128971 => @lem7010331 _128971 f u v h0 h1 h2 h3). Qed.
Lemma lem7010333 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : term39 _128971 u v f.
Proof. exact (fun h0 : term21 _128971 u v f => @lem7010332 _128971 f u v h1 h0 h2). Qed.
Lemma lem7010334 {_128971 : Type'} (u : _128971 -> Prop) (f : _128971 -> nat) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : term42 _128971 u v f.
Proof. exact (fun h0 : @SUBSET _128971 u v => @lem7010333 _128971 f u v h1 h0). Qed.
Lemma lem7010335 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term44 _128971 u v f.
Proof. exact (fun h0 : @FINITE _128971 v => @lem7010334 _128971 u f v h0). Qed.
Lemma lem7010340 {_128971 : Type'} (v : _128971 -> Prop) (f : _128971 -> nat) : term48 _128971 v f.
Proof. exact (fun u : _128971 -> Prop => @lem7010335 _128971 u v f). Qed.
Lemma lem7010345 {_128971 : Type'} (f : _128971 -> nat) : term52 _128971 f.
Proof. exact (fun v : _128971 -> Prop => @lem7010340 _128971 v f). Qed.
Lemma lem7010350 {_128971 : Type'} : term56 _128971.
Proof. exact (fun f : _128971 -> nat => @lem7010345 _128971 f). Qed.
Lemma lem7010351 {_128971 : Type'} : term55 _128971.
Proof. exact (EQ_MP (@lem7007290 _128971) (@lem7010350 _128971)). Qed.
Lemma lem7010352 {_128971 : Type'} (f : _128971 -> nat) : term495 _128971 f.
Proof. exact (@lem7010351 _128971 f). Qed.
Lemma lem7010353 {_128971 : Type'} (f : _128971 -> nat) : (term495 _128971 f) = (term51 _128971 f).
Proof. exact (eq_refl (term495 _128971 f)). Qed.
Lemma lem7010354 {_128971 : Type'} (f : _128971 -> nat) : term51 _128971 f.
Proof. exact (EQ_MP (@lem7010353 _128971 f) (@lem7010352 _128971 f)). Qed.
Lemma lem7010355 {_128971 : Type'} (f : _128971 -> nat) (v : _128971 -> Prop) : term496 _128971 f v.
Proof. exact (@lem7010354 _128971 f v). Qed.
Lemma lem7010356 {_128971 : Type'} (v : _128971 -> Prop) (f : _128971 -> nat) : (term496 _128971 f v) = (term47 _128971 v f).
Proof. exact (eq_refl (term496 _128971 f v)). Qed.
Lemma lem7010357 {_128971 : Type'} (v : _128971 -> Prop) (f : _128971 -> nat) : term47 _128971 v f.
Proof. exact (EQ_MP (@lem7010356 _128971 v f) (@lem7010355 _128971 f v)). Qed.
Lemma lem7010358 {_128971 : Type'} (v : _128971 -> Prop) (f : _128971 -> nat) (u : _128971 -> Prop) : term497 _128971 v f u.
Proof. exact (@lem7010357 _128971 v f u). Qed.
Lemma lem7010359 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term497 _128971 v f u) = (term25 _128971 u v f).
Proof. exact (eq_refl (term497 _128971 v f u)). Qed.
Lemma lem7010360 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term25 _128971 u v f.
Proof. exact (EQ_MP (@lem7010359 _128971 u v f) (@lem7010358 _128971 v f u)). Qed.
Lemma lem7010362 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term25 _128971 u v f.
Proof. exact (@lem7006971 _128971 u v f (@lem7010360 _128971 u v f)). Qed.
Lemma lem7010363 {_128971 : Type'} (u : _128971 -> Prop) (f : _128971 -> nat) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) : term41 _128971 u v f.
Proof. exact (@lem7010362 _128971 u v f (@lem7006941 _128971 v h1)). Qed.
Lemma lem7010364 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : term38 _128971 u v f.
Proof. exact (@lem7010363 _128971 u f v h1 (@lem7006940 _128971 u v h2)). Qed.
Lemma lem7010365 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term21 _128971 u v f) (h3 : @SUBSET _128971 u v) : term35 _128971.
Proof. exact (@lem7010364 _128971 f u v h1 h3 (@lem7006949 _128971 u v f h2)). Qed.
Lemma lem7010366 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term21 _128971 u v f) (h3 : @SUBSET _128971 u v) : term32 _128971.
Proof. exact (@lem7010365 _128971 f u v h1 h2 h3 (@lem7006954 _128971)). Qed.
Lemma lem7010367 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term21 _128971 u v f) (h3 : @SUBSET _128971 u v) : term29 _128971.
Proof. exact (@lem7010366 _128971 f u v h1 h2 h3 (@lem7006952 _128971)). Qed.
Lemma lem7010368 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term21 _128971 u v f) (h3 : @SUBSET _128971 u v) : False.
Proof. exact (@lem7010367 _128971 f u v h1 h2 h3 (@lem7006950 _128971)). Qed.
Lemma lem7010369 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term21 _128971 u v f) (h3 : @SUBSET _128971 u v) : (term21 _128971 u v f) = False.
Proof. exact (prop_ext (fun h4 : term21 _128971 u v f => @lem7010368 _128971 f u v h1 h2 h3) (fun h4 : False => @lem7006949 _128971 u v f h2)). Qed.
Lemma lem7010370 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term21 _128971 u v f) (h3 : @SUBSET _128971 u v) : False.
Proof. exact (EQ_MP (@lem7010369 _128971 f u v h1 h2 h3) (@lem7006949 _128971 u v f h2)). Qed.
Lemma lem7010371 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : term20 _128971 u v f.
Proof. exact (fun h0 : term21 _128971 u v f => @lem7010370 _128971 f u v h1 h0 h2). Qed.
Lemma lem7010372 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : term14 _128971 u v f.
Proof. exact (EQ_MP (@lem7006948 _128971 u v f) (@lem7010371 _128971 f u v h1 h2)). Qed.
Lemma lem7010373 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : term15 _128971 u v f.
Proof. exact (@lem7006944 _128971 u v f (@lem7010372 _128971 f u v h1 h2)). Qed.
Lemma lem7010374 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term18 _128971 u v) : @SUBSET _128971 u v.
Proof. exact (proj2 (@lem7006939 _128971 u v h1)). Qed.
Lemma lem7010375 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term18 _128971 u v) : @FINITE _128971 v.
Proof. exact (proj1 (@lem7006939 _128971 u v h1)). Qed.
Lemma lem7010376 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : (@SUBSET _128971 u v) = (term15 _128971 u v f).
Proof. exact (prop_ext (fun h3 : @SUBSET _128971 u v => @lem7010373 _128971 f u v h1 h2) (fun h3 : term15 _128971 u v f => @lem7006940 _128971 u v h2)). Qed.
Lemma lem7010377 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : term15 _128971 u v f.
Proof. exact (EQ_MP (@lem7010376 _128971 f u v h1 h2) (@lem7006940 _128971 u v h2)). Qed.
Lemma lem7010378 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : (@FINITE _128971 v) = (term15 _128971 u v f).
Proof. exact (prop_ext (fun h3 : @FINITE _128971 v => @lem7010377 _128971 f u v h1 h2) (fun h3 : term15 _128971 u v f => @lem7006941 _128971 v h1)). Qed.
Lemma lem7010379 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : @SUBSET _128971 u v) : term15 _128971 u v f.
Proof. exact (EQ_MP (@lem7010378 _128971 f u v h1 h2) (@lem7006941 _128971 v h1)). Qed.
Lemma lem7010380 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term18 _128971 u v) : (@SUBSET _128971 u v) = (term15 _128971 u v f).
Proof. exact (prop_ext (fun h3 : @SUBSET _128971 u v => @lem7010379 _128971 f u v h1 h3) (fun h3 : term15 _128971 u v f => @lem7010374 _128971 u v h2)). Qed.
Lemma lem7010381 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : @FINITE _128971 v) (h2 : term18 _128971 u v) : term15 _128971 u v f.
Proof. exact (EQ_MP (@lem7010380 _128971 f u v h1 h2) (@lem7010374 _128971 u v h2)). Qed.
Lemma lem7010382 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term18 _128971 u v) : (@FINITE _128971 v) = (term15 _128971 u v f).
Proof. exact (prop_ext (fun h2 : @FINITE _128971 v => @lem7010381 _128971 f u v h2 h1) (fun h2 : term15 _128971 u v f => @lem7010375 _128971 u v h1)). Qed.
Lemma lem7010383 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term18 _128971 u v) : term15 _128971 u v f.
Proof. exact (EQ_MP (@lem7010382 _128971 f u v h1) (@lem7010375 _128971 u v h1)). Qed.
Lemma lem7010384 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term498 _128971 u v f.
Proof. exact (fun h0 : term18 _128971 u v => @lem7010383 _128971 f u v h0). Qed.
Lemma lem7010389 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : term499 _128971 u v.
Proof. exact (fun f : _128971 -> nat => @lem7010384 _128971 u v f). Qed.
Lemma lem7010394 {_128971 : Type'} (u : _128971 -> Prop) : term500 _128971 u.
Proof. exact (fun v : _128971 -> Prop => @lem7010389 _128971 u v). Qed.
Lemma lem7010399 {_128971 : Type'} : term501 _128971.
Proof. exact (fun u : _128971 -> Prop => @lem7010394 _128971 u). Qed.
