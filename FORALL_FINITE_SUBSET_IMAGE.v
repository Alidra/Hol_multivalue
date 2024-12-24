Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_FINITE_SUBSET_IMAGE_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import EXISTS_FINITE_SUBSET_IMAGE_spec.
Require Import NOT_IMP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem3693978 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3693979 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (SYM (@lem3693978 t1 t2 t3 h1)). Qed.
Lemma lem3693980 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3693981 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (SYM (@lem3693980 t1 t2 t3 h1)). Qed.
Lemma lem3693982 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term0 t1 t2 t3) = (term1 t1 t2 t3)) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3) => @lem3693979 t1 t2 t3 h1) (fun h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3) => @lem3693981 t1 t2 t3 h1)). Qed.
Lemma lem3693983 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem3693982 t1 t2 t3)). Qed.
Lemma lem3693984 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3693985 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (MK_COMB (@lem3693984) (@lem3693983 t1 t2)). Qed.
Lemma lem3693986 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem3693985 t1 t2)). Qed.
Lemma lem3693987 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3693988 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (MK_COMB (@lem3693987) (@lem3693986 t1)). Qed.
Lemma lem3693989 : term10 = term11.
Proof. exact (fun_ext (fun t1 : Prop => @lem3693988 t1)). Qed.
Lemma lem3693990 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3693991 : term12 = term13.
Proof. exact (MK_COMB (@lem3693990) (@lem3693989)). Qed.
Lemma lem3693992 : term13.
Proof. exact (EQ_MP (@lem3693991) (@lem512)). Qed.
Lemma lem3693993 {_93804 _93824 : Type'} (P : type686 _93824) : term14 _93804 _93824 P.
Proof. exact (@lem3693974 _93804 _93824 P). Qed.
Lemma lem3693994 {_93804 _93824 : Type'} (P : type686 _93824) : (term14 _93804 _93824 P) = (term15 _93804 _93824 P).
Proof. exact (eq_refl (term14 _93804 _93824 P)). Qed.
Lemma lem3693995 {_93804 _93824 : Type'} (P : type686 _93824) : term15 _93804 _93824 P.
Proof. exact (EQ_MP (@lem3693994 _93804 _93824 P) (@lem3693993 _93804 _93824 P)). Qed.
Lemma lem3693996 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : term16 _93804 _93824 P f.
Proof. exact (@lem3693995 _93804 _93824 P f). Qed.
Lemma lem3693997 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : (term16 _93804 _93824 P f) = (term17 _93804 _93824 P f).
Proof. exact (eq_refl (term16 _93804 _93824 P f)). Qed.
Lemma lem3693998 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : term17 _93804 _93824 P f.
Proof. exact (EQ_MP (@lem3693997 _93804 _93824 P f) (@lem3693996 _93804 _93824 P f)). Qed.
Lemma lem3693999 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (s : _93804 -> Prop) : term18 _93804 _93824 P f s.
Proof. exact (@lem3693998 _93804 _93824 P f s). Qed.
Lemma lem3694000 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term18 _93804 _93824 P f s) = ((term19 _93804 _93824 f s P) = (term20 _93804 _93824 s P f)).
Proof. exact (eq_refl (term18 _93804 _93824 P f s)). Qed.
Lemma lem3694002 (t1 : Prop) : term21 t1.
Proof. exact (@lem3693992 t1). Qed.
Lemma lem3694003 (t1 : Prop) : (term21 t1) = (term9 t1).
Proof. exact (eq_refl (term21 t1)). Qed.
Lemma lem3694004 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem3694003 t1) (@lem3694002 t1)). Qed.
Lemma lem3694005 (t1 : Prop) (t2 : Prop) : term22 t1 t2.
Proof. exact (@lem3694004 t1 t2). Qed.
Lemma lem3694006 (t1 : Prop) (t2 : Prop) : (term22 t1 t2) = (term5 t1 t2).
Proof. exact (eq_refl (term22 t1 t2)). Qed.
Lemma lem3694007 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (EQ_MP (@lem3694006 t1 t2) (@lem3694005 t1 t2)). Qed.
Lemma lem3694008 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term23 t1 t2 t3.
Proof. exact (@lem3694007 t1 t2 t3). Qed.
Lemma lem3694009 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term23 t1 t2 t3) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (eq_refl (term23 t1 t2 t3)). Qed.
Lemma lem3694011 (t1 : Prop) : term24 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem3694012 (t1 : Prop) : (term24 t1) = (term25 t1).
Proof. exact (eq_refl (term24 t1)). Qed.
Lemma lem3694013 (t1 : Prop) : term25 t1.
Proof. exact (EQ_MP (@lem3694012 t1) (@lem3694011 t1)). Qed.
Lemma lem3694014 (t1 : Prop) (t2 : Prop) : term26 t1 t2.
Proof. exact (@lem3694013 t1 t2). Qed.
Lemma lem3694015 (t1 : Prop) (t2 : Prop) : (term26 t1 t2) = ((term27 t1 t2) = (term28 t1 t2)).
Proof. exact (eq_refl (term26 t1 t2)). Qed.
Lemma lem3694028 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3694029 {_93839 : Type'} (P : _93839 -> Prop) : ((term30 _93839 P) = (term31 _93839 P)) = (term32 _93839 P).
Proof. exact (@lem3694028 ((term30 _93839 P) = (term31 _93839 P))). Qed.
Lemma lem3694030 {_93839 : Type'} (P : _93839 -> Prop) : (term32 _93839 P) = ((term30 _93839 P) = (term31 _93839 P)).
Proof. exact (SYM (@lem3694029 _93839 P)). Qed.
Lemma lem3694031 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : term33 _93839 P.
Proof. exact (h1). Qed.
Lemma lem3694034 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term32 _93839 P) : term32 _93839 P.
Proof. exact (h1). Qed.
Lemma lem3694035 {_93839 : Type'} (P : _93839 -> Prop) : term34 _93839 P.
Proof. exact (fun h0 : term32 _93839 P => @lem3694034 _93839 P h0). Qed.
Lemma lem3694036 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term34 _93839 P) : term34 _93839 P.
Proof. exact (h1). Qed.
Lemma lem3694037 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term32 _93839 P) : term32 _93839 P.
Proof. exact (h1). Qed.
Lemma lem3694038 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term32 _93839 P) (h2 : term34 _93839 P) : term32 _93839 P.
Proof. exact (@lem3694036 _93839 P h2 (@lem3694037 _93839 P h1)). Qed.
Lemma lem3694039 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term32 _93839 P) : term35 _93839 P.
Proof. exact (fun h0 : term34 _93839 P => @lem3694038 _93839 P h1 h0). Qed.
Lemma lem3694040 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term34 _93839 P) : term34 _93839 P.
Proof. exact (h1). Qed.
Lemma lem3694041 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term32 _93839 P) (h2 : term34 _93839 P) : term32 _93839 P.
Proof. exact (@lem3694039 _93839 P h1 (@lem3694040 _93839 P h2)). Qed.
Lemma lem3694042 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term34 _93839 P) : term34 _93839 P.
Proof. exact (fun h0 : term32 _93839 P => @lem3694041 _93839 P h0 h1). Qed.
Lemma lem3694043 {_93839 : Type'} (P : _93839 -> Prop) : term36 _93839 P.
Proof. exact (fun h0 : term34 _93839 P => @lem3694042 _93839 P h0). Qed.
Lemma lem3694046 {_93839 : Type'} (P : _93839 -> Prop) : term34 _93839 P.
Proof. exact (@lem3694043 _93839 P (@lem3694035 _93839 P)). Qed.
Lemma lem3694047 {_93839 : Type'} (P : _93839 -> Prop) : term34 _93839 P.
Proof. exact (@lem3694046 _93839 P). Qed.
Lemma lem3694053 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3694054 {_93839 : Type'} (P : _93839 -> Prop) : (term32 _93839 P) = (term37 _93839 P).
Proof. exact (@lem3694053 (term33 _93839 P)). Qed.
Lemma lem3694056 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3694057 {_93839 : Type'} (P : _93839 -> Prop) : (term37 _93839 P) = ((term30 _93839 P) = (term31 _93839 P)).
Proof. exact (@lem3694056 ((term30 _93839 P) = (term31 _93839 P))). Qed.
Lemma lem3694058 {_93839 : Type'} (P : _93839 -> Prop) : (term32 _93839 P) = ((term30 _93839 P) = (term31 _93839 P)).
Proof. exact (TRANS (@lem3694054 _93839 P) (@lem3694057 _93839 P)). Qed.
Lemma lem3694067 {_93839 : Type'} : (term39 _93839) = (term40 _93839).
Proof. exact (fun_ext (fun P : _93839 -> Prop => @lem3694058 _93839 P)). Qed.
Lemma lem3694068 {_93839 : Type'} : (@all (_93839 -> Prop)) = (@all (_93839 -> Prop)).
Proof. exact (eq_refl (@all (_93839 -> Prop))). Qed.
Lemma lem3694077 {_93839 : Type'} : (term41 _93839) = (term42 _93839).
Proof. exact (MK_COMB (@lem3694068 _93839) (@lem3694067 _93839)). Qed.
Lemma lem3694080 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term43 _93839 P x) = (term43 _93839 P x).
Proof. exact (eq_refl (term43 _93839 P x)). Qed.
Lemma lem3694081 {_93839 : Type'} (P : _93839 -> Prop) : (term44 _93839 P) = (term44 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694080 _93839 P x)). Qed.
Lemma lem3694082 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694083 {_93839 : Type'} (P : _93839 -> Prop) : (term45 _93839 P) = (term45 _93839 P).
Proof. exact (MK_COMB (@lem3694082 _93839) (@lem3694081 _93839 P)). Qed.
Lemma lem3694084 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694085 {_93839 : Type'} (P : _93839 -> Prop) : (term31 _93839 P) = (term31 _93839 P).
Proof. exact (MK_COMB (@lem3694084) (@lem3694083 _93839 P)). Qed.
Lemma lem3694086 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3694087 {_93839 : Type'} (P : _93839 -> Prop) : (term46 _93839 P) = (term46 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694086 _93839 P x)). Qed.
Lemma lem3694088 {_93839 : Type'} : (@all _93839) = (@all _93839).
Proof. exact (eq_refl (@all _93839)). Qed.
Lemma lem3694089 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term30 _93839 P).
Proof. exact (MK_COMB (@lem3694088 _93839) (@lem3694087 _93839 P)). Qed.
Lemma lem3694090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694091 {_93839 : Type'} (P : _93839 -> Prop) : (term47 _93839 P) = (term47 _93839 P).
Proof. exact (MK_COMB (@lem3694090) (@lem3694089 _93839 P)). Qed.
Lemma lem3694092 {_93839 : Type'} (P : _93839 -> Prop) : ((term30 _93839 P) = (term31 _93839 P)) = ((term30 _93839 P) = (term31 _93839 P)).
Proof. exact (MK_COMB (@lem3694091 _93839 P) (@lem3694085 _93839 P)). Qed.
Lemma lem3694093 {_93839 : Type'} : (term40 _93839) = (term40 _93839).
Proof. exact (fun_ext (fun P : _93839 -> Prop => @lem3694092 _93839 P)). Qed.
Lemma lem3694094 {_93839 : Type'} : (@all (_93839 -> Prop)) = (@all (_93839 -> Prop)).
Proof. exact (eq_refl (@all (_93839 -> Prop))). Qed.
Lemma lem3694095 {_93839 : Type'} : (term42 _93839) = (term42 _93839).
Proof. exact (MK_COMB (@lem3694094 _93839) (@lem3694093 _93839)). Qed.
Lemma lem3694116 {_93839 : Type'} : (term41 _93839) = (term42 _93839).
Proof. exact (TRANS (@lem3694077 _93839) (@lem3694095 _93839)). Qed.
Lemma lem3694117 {_93839 : Type'} : (term42 _93839) = (term41 _93839).
Proof. exact (SYM (@lem3694116 _93839)). Qed.
Lemma lem3694119 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3694120 {_93839 : Type'} (P : _93839 -> Prop) : ((term30 _93839 P) = (term31 _93839 P)) = (term32 _93839 P).
Proof. exact (@lem3694119 ((term30 _93839 P) = (term31 _93839 P))). Qed.
Lemma lem3694121 {_93839 : Type'} (P : _93839 -> Prop) : (term32 _93839 P) = ((term30 _93839 P) = (term31 _93839 P)).
Proof. exact (SYM (@lem3694120 _93839 P)). Qed.
Lemma lem3694122 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : term33 _93839 P.
Proof. exact (h1). Qed.
Lemma lem3694124 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3694125 {_93839 : Type'} (P : _93839 -> Prop) : (term48 _93839 P) = (term45 _93839 P).
Proof. exact (@lem18392 _93839 P). Qed.
Lemma lem3694126 {_93839 : Type'} (P : _93839 -> Prop) : (term49 _93839 P) = (term50 _93839 P).
Proof. exact (@lem3694125 _93839 (term46 _93839 P)). Qed.
Lemma lem3694127 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term51 _93839 P x) = (P x).
Proof. exact (eq_refl (term51 _93839 P x)). Qed.
Lemma lem3694128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694130 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term52 _93839 P x) = (term43 _93839 P x).
Proof. exact (MK_COMB (@lem3694128) (@lem3694127 _93839 P x)). Qed.
Lemma lem3694131 {_93839 : Type'} (P : _93839 -> Prop) : (term53 _93839 P) = (term44 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694130 _93839 P x)). Qed.
Lemma lem3694132 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694133 {_93839 : Type'} (P : _93839 -> Prop) : (term50 _93839 P) = (term45 _93839 P).
Proof. exact (MK_COMB (@lem3694132 _93839) (@lem3694131 _93839 P)). Qed.
Lemma lem3694134 {_93839 : Type'} (P : _93839 -> Prop) : (term49 _93839 P) = (term45 _93839 P).
Proof. exact (TRANS (@lem3694126 _93839 P) (@lem3694133 _93839 P)). Qed.
Lemma lem3694135 {_93839 : Type'} (P : _93839 -> Prop) : (term46 _93839 P) = (term46 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694124 _93839 P x)). Qed.
Lemma lem3694136 {_93839 : Type'} : (@all _93839) = (@all _93839).
Proof. exact (eq_refl (@all _93839)). Qed.
Lemma lem3694137 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term30 _93839 P).
Proof. exact (MK_COMB (@lem3694136 _93839) (@lem3694135 _93839 P)). Qed.
Lemma lem3694138 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term43 _93839 P x) = (term43 _93839 P x).
Proof. exact (eq_refl (term43 _93839 P x)). Qed.
Lemma lem3694141 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term54 _93839 P x) = (P x).
Proof. exact (@lem16933 (P x)). Qed.
Lemma lem3694142 {_93839 : Type'} (P : _93839 -> Prop) : (term55 _93839 P) = (term56 _93839 P).
Proof. exact (@lem18394 _93839 P). Qed.
Lemma lem3694143 {_93839 : Type'} (P : _93839 -> Prop) : (term31 _93839 P) = (term57 _93839 P).
Proof. exact (@lem3694142 _93839 (term44 _93839 P)). Qed.
Lemma lem3694144 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term58 _93839 P x) = (term43 _93839 P x).
Proof. exact (eq_refl (term58 _93839 P x)). Qed.
Lemma lem3694145 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694146 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term59 _93839 P x) = (term54 _93839 P x).
Proof. exact (MK_COMB (@lem3694145) (@lem3694144 _93839 P x)). Qed.
Lemma lem3694147 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term59 _93839 P x) = (P x).
Proof. exact (TRANS (@lem3694146 _93839 P x) (@lem3694141 _93839 P x)). Qed.
Lemma lem3694148 {_93839 : Type'} (P : _93839 -> Prop) : (term60 _93839 P) = (term46 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694147 _93839 P x)). Qed.
Lemma lem3694149 {_93839 : Type'} : (@all _93839) = (@all _93839).
Proof. exact (eq_refl (@all _93839)). Qed.
Lemma lem3694150 {_93839 : Type'} (P : _93839 -> Prop) : (term57 _93839 P) = (term30 _93839 P).
Proof. exact (MK_COMB (@lem3694149 _93839) (@lem3694148 _93839 P)). Qed.
Lemma lem3694151 {_93839 : Type'} (P : _93839 -> Prop) : (term31 _93839 P) = (term30 _93839 P).
Proof. exact (TRANS (@lem3694143 _93839 P) (@lem3694150 _93839 P)). Qed.
Lemma lem3694152 {_93839 : Type'} (P : _93839 -> Prop) : (term44 _93839 P) = (term44 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694138 _93839 P x)). Qed.
Lemma lem3694153 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694154 {_93839 : Type'} (P : _93839 -> Prop) : (term45 _93839 P) = (term45 _93839 P).
Proof. exact (MK_COMB (@lem3694153 _93839) (@lem3694152 _93839 P)). Qed.
Lemma lem3694155 {_93839 : Type'} (P : _93839 -> Prop) : (term61 _93839 P) = (term45 _93839 P).
Proof. exact (@lem16933 (term45 _93839 P)). Qed.
Lemma lem3694156 {_93839 : Type'} (P : _93839 -> Prop) : (term61 _93839 P) = (term45 _93839 P).
Proof. exact (TRANS (@lem3694155 _93839 P) (@lem3694154 _93839 P)). Qed.
Lemma lem3694157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3694158 {_93839 : Type'} (P : _93839 -> Prop) : (term62 _93839 P) = (term63 _93839 P).
Proof. exact (MK_COMB (@lem3694157) (@lem3694134 _93839 P)). Qed.
Lemma lem3694159 {_93839 : Type'} (P : _93839 -> Prop) : (term64 _93839 P) = (term65 _93839 P).
Proof. exact (MK_COMB (@lem3694158 _93839 P) (@lem3694151 _93839 P)). Qed.
Lemma lem3694160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3694161 {_93839 : Type'} (P : _93839 -> Prop) : (term66 _93839 P) = (term66 _93839 P).
Proof. exact (MK_COMB (@lem3694160) (@lem3694137 _93839 P)). Qed.
Lemma lem3694162 {_93839 : Type'} (P : _93839 -> Prop) : (term67 _93839 P) = (term68 _93839 P).
Proof. exact (MK_COMB (@lem3694161 _93839 P) (@lem3694156 _93839 P)). Qed.
Lemma lem3694163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3694164 {_93839 : Type'} (P : _93839 -> Prop) : (term69 _93839 P) = (term70 _93839 P).
Proof. exact (MK_COMB (@lem3694163) (@lem3694162 _93839 P)). Qed.
Lemma lem3694165 {_93839 : Type'} (P : _93839 -> Prop) : (term71 _93839 P) = (term72 _93839 P).
Proof. exact (MK_COMB (@lem3694164 _93839 P) (@lem3694159 _93839 P)). Qed.
Lemma lem3694166 {_93839 : Type'} (P : _93839 -> Prop) : (term33 _93839 P) = (term71 _93839 P).
Proof. exact (@lem17646 (term30 _93839 P) (term31 _93839 P)). Qed.
Lemma lem3694167 {_93839 : Type'} (P : _93839 -> Prop) : (term33 _93839 P) = (term72 _93839 P).
Proof. exact (TRANS (@lem3694166 _93839 P) (@lem3694165 _93839 P)). Qed.
Lemma lem3694186 {A : Type'} (P : Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3694187 {_93839 : Type'} (P : Prop) (Q : _93839 -> Prop) : (term73 _93839 P Q) = (term74 _93839 P Q).
Proof. exact (@lem3694186 _93839 P Q). Qed.
Lemma lem3694188 {_93839 : Type'} (P : _93839 -> Prop) : (term75 _93839 P) = (term76 _93839 P).
Proof. exact (@lem3694187 _93839 (term30 _93839 P) (term44 _93839 P)). Qed.
Lemma lem3694189 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term58 _93839 P x) = (term43 _93839 P x).
Proof. exact (eq_refl (term58 _93839 P x)). Qed.
Lemma lem3694190 {_93839 : Type'} (P : _93839 -> Prop) : (term77 _93839 P) = (term44 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694189 _93839 P x)). Qed.
Lemma lem3694191 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694192 {_93839 : Type'} (P : _93839 -> Prop) : (term78 _93839 P) = (term45 _93839 P).
Proof. exact (MK_COMB (@lem3694191 _93839) (@lem3694190 _93839 P)). Qed.
Lemma lem3694193 {_93839 : Type'} (P : _93839 -> Prop) : (term66 _93839 P) = (term66 _93839 P).
Proof. exact (eq_refl (term66 _93839 P)). Qed.
Lemma lem3694194 {_93839 : Type'} (P : _93839 -> Prop) : (term75 _93839 P) = (term68 _93839 P).
Proof. exact (MK_COMB (@lem3694193 _93839 P) (@lem3694192 _93839 P)). Qed.
Lemma lem3694195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694196 {_93839 : Type'} (P : _93839 -> Prop) : (term79 _93839 P) = (term80 _93839 P).
Proof. exact (MK_COMB (@lem3694195) (@lem3694194 _93839 P)). Qed.
Lemma lem3694197 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term58 _93839 P x) = (term43 _93839 P x).
Proof. exact (eq_refl (term58 _93839 P x)). Qed.
Lemma lem3694198 {_93839 : Type'} (P : _93839 -> Prop) : (term66 _93839 P) = (term66 _93839 P).
Proof. exact (eq_refl (term66 _93839 P)). Qed.
Lemma lem3694199 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term81 _93839 P x) = (term82 _93839 P x).
Proof. exact (MK_COMB (@lem3694198 _93839 P) (@lem3694197 _93839 P x)). Qed.
Lemma lem3694200 {_93839 : Type'} (P : _93839 -> Prop) : (term83 _93839 P) = (term84 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694199 _93839 P x)). Qed.
Lemma lem3694201 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694202 {_93839 : Type'} (P : _93839 -> Prop) : (term76 _93839 P) = (term85 _93839 P).
Proof. exact (MK_COMB (@lem3694201 _93839) (@lem3694200 _93839 P)). Qed.
Lemma lem3694203 {_93839 : Type'} (P : _93839 -> Prop) : ((term75 _93839 P) = (term76 _93839 P)) = ((term68 _93839 P) = (term85 _93839 P)).
Proof. exact (MK_COMB (@lem3694196 _93839 P) (@lem3694202 _93839 P)). Qed.
Lemma lem3694204 {_93839 : Type'} (P : _93839 -> Prop) : (term68 _93839 P) = (term85 _93839 P).
Proof. exact (EQ_MP (@lem3694203 _93839 P) (@lem3694188 _93839 P)). Qed.
Lemma lem3694205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3694206 {_93839 : Type'} (P : _93839 -> Prop) : (term70 _93839 P) = (term86 _93839 P).
Proof. exact (MK_COMB (@lem3694205) (@lem3694204 _93839 P)). Qed.
Lemma lem3694208 {A : Type'} (P : A -> Prop) (Q : Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3694209 {_93839 : Type'} (P : _93839 -> Prop) (Q : Prop) : (term87 _93839 P Q) = (term88 _93839 P Q).
Proof. exact (@lem3694208 _93839 P Q). Qed.
Lemma lem3694210 {_93839 : Type'} (P : _93839 -> Prop) : (term89 _93839 P) = (term90 _93839 P).
Proof. exact (@lem3694209 _93839 (term44 _93839 P) (term30 _93839 P)). Qed.
Lemma lem3694211 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term58 _93839 P x) = (term43 _93839 P x).
Proof. exact (eq_refl (term58 _93839 P x)). Qed.
Lemma lem3694212 {_93839 : Type'} (P : _93839 -> Prop) : (term77 _93839 P) = (term44 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694211 _93839 P x)). Qed.
Lemma lem3694213 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694214 {_93839 : Type'} (P : _93839 -> Prop) : (term78 _93839 P) = (term45 _93839 P).
Proof. exact (MK_COMB (@lem3694213 _93839) (@lem3694212 _93839 P)). Qed.
Lemma lem3694215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3694216 {_93839 : Type'} (P : _93839 -> Prop) : (term91 _93839 P) = (term63 _93839 P).
Proof. exact (MK_COMB (@lem3694215) (@lem3694214 _93839 P)). Qed.
Lemma lem3694217 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term30 _93839 P).
Proof. exact (eq_refl (term30 _93839 P)). Qed.
Lemma lem3694218 {_93839 : Type'} (P : _93839 -> Prop) : (term89 _93839 P) = (term65 _93839 P).
Proof. exact (MK_COMB (@lem3694216 _93839 P) (@lem3694217 _93839 P)). Qed.
Lemma lem3694219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694220 {_93839 : Type'} (P : _93839 -> Prop) : (term92 _93839 P) = (term93 _93839 P).
Proof. exact (MK_COMB (@lem3694219) (@lem3694218 _93839 P)). Qed.
Lemma lem3694221 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term58 _93839 P x) = (term43 _93839 P x).
Proof. exact (eq_refl (term58 _93839 P x)). Qed.
Lemma lem3694222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3694223 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term94 _93839 P x) = (term95 _93839 P x).
Proof. exact (MK_COMB (@lem3694222) (@lem3694221 _93839 P x)). Qed.
Lemma lem3694224 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term30 _93839 P).
Proof. exact (eq_refl (term30 _93839 P)). Qed.
Lemma lem3694225 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) : (term96 _93839 x P) = (term97 _93839 x P).
Proof. exact (MK_COMB (@lem3694223 _93839 P x) (@lem3694224 _93839 P)). Qed.
Lemma lem3694226 {_93839 : Type'} (P : _93839 -> Prop) : (term98 _93839 P) = (term99 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694225 _93839 x P)). Qed.
Lemma lem3694227 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694228 {_93839 : Type'} (P : _93839 -> Prop) : (term90 _93839 P) = (term100 _93839 P).
Proof. exact (MK_COMB (@lem3694227 _93839) (@lem3694226 _93839 P)). Qed.
Lemma lem3694229 {_93839 : Type'} (P : _93839 -> Prop) : ((term89 _93839 P) = (term90 _93839 P)) = ((term65 _93839 P) = (term100 _93839 P)).
Proof. exact (MK_COMB (@lem3694220 _93839 P) (@lem3694228 _93839 P)). Qed.
Lemma lem3694230 {_93839 : Type'} (P : _93839 -> Prop) : (term65 _93839 P) = (term100 _93839 P).
Proof. exact (EQ_MP (@lem3694229 _93839 P) (@lem3694210 _93839 P)). Qed.
Lemma lem3694231 {_93839 : Type'} (P : _93839 -> Prop) : (term72 _93839 P) = (term101 _93839 P).
Proof. exact (MK_COMB (@lem3694206 _93839 P) (@lem3694230 _93839 P)). Qed.
Lemma lem3694233 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3694234 {_93839 : Type'} (P : _93839 -> Prop) (Q : _93839 -> Prop) : (term102 _93839 P Q) = (term103 _93839 P Q).
Proof. exact (@lem3694233 _93839 P Q). Qed.
Lemma lem3694235 {_93839 : Type'} (P : _93839 -> Prop) : (term104 _93839 P) = (term105 _93839 P).
Proof. exact (@lem3694234 _93839 (term84 _93839 P) (term99 _93839 P)). Qed.
Lemma lem3694236 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term106 _93839 P x) = (term82 _93839 P x).
Proof. exact (eq_refl (term106 _93839 P x)). Qed.
Lemma lem3694237 {_93839 : Type'} (P : _93839 -> Prop) : (term107 _93839 P) = (term84 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694236 _93839 P x)). Qed.
Lemma lem3694238 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694239 {_93839 : Type'} (P : _93839 -> Prop) : (term108 _93839 P) = (term85 _93839 P).
Proof. exact (MK_COMB (@lem3694238 _93839) (@lem3694237 _93839 P)). Qed.
Lemma lem3694240 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3694241 {_93839 : Type'} (P : _93839 -> Prop) : (term109 _93839 P) = (term86 _93839 P).
Proof. exact (MK_COMB (@lem3694240) (@lem3694239 _93839 P)). Qed.
Lemma lem3694242 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) : (term110 _93839 P x) = (term97 _93839 x P).
Proof. exact (eq_refl (term110 _93839 P x)). Qed.
Lemma lem3694243 {_93839 : Type'} (P : _93839 -> Prop) : (term111 _93839 P) = (term99 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694242 _93839 x P)). Qed.
Lemma lem3694244 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694245 {_93839 : Type'} (P : _93839 -> Prop) : (term112 _93839 P) = (term100 _93839 P).
Proof. exact (MK_COMB (@lem3694244 _93839) (@lem3694243 _93839 P)). Qed.
Lemma lem3694246 {_93839 : Type'} (P : _93839 -> Prop) : (term104 _93839 P) = (term101 _93839 P).
Proof. exact (MK_COMB (@lem3694241 _93839 P) (@lem3694245 _93839 P)). Qed.
Lemma lem3694247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694248 {_93839 : Type'} (P : _93839 -> Prop) : (term113 _93839 P) = (term114 _93839 P).
Proof. exact (MK_COMB (@lem3694247) (@lem3694246 _93839 P)). Qed.
Lemma lem3694249 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term106 _93839 P x) = (term82 _93839 P x).
Proof. exact (eq_refl (term106 _93839 P x)). Qed.
Lemma lem3694250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3694251 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term115 _93839 P x) = (term116 _93839 P x).
Proof. exact (MK_COMB (@lem3694250) (@lem3694249 _93839 P x)). Qed.
Lemma lem3694252 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) : (term110 _93839 P x) = (term97 _93839 x P).
Proof. exact (eq_refl (term110 _93839 P x)). Qed.
Lemma lem3694253 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) : (term117 _93839 P x) = (term118 _93839 x P).
Proof. exact (MK_COMB (@lem3694251 _93839 P x) (@lem3694252 _93839 x P)). Qed.
Lemma lem3694254 {_93839 : Type'} (P : _93839 -> Prop) : (term119 _93839 P) = (term120 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694253 _93839 x P)). Qed.
Lemma lem3694255 {_93839 : Type'} : (@ex _93839) = (@ex _93839).
Proof. exact (eq_refl (@ex _93839)). Qed.
Lemma lem3694256 {_93839 : Type'} (P : _93839 -> Prop) : (term105 _93839 P) = (term121 _93839 P).
Proof. exact (MK_COMB (@lem3694255 _93839) (@lem3694254 _93839 P)). Qed.
Lemma lem3694257 {_93839 : Type'} (P : _93839 -> Prop) : ((term104 _93839 P) = (term105 _93839 P)) = ((term101 _93839 P) = (term121 _93839 P)).
Proof. exact (MK_COMB (@lem3694248 _93839 P) (@lem3694256 _93839 P)). Qed.
Lemma lem3694258 {_93839 : Type'} (P : _93839 -> Prop) : (term101 _93839 P) = (term121 _93839 P).
Proof. exact (EQ_MP (@lem3694257 _93839 P) (@lem3694235 _93839 P)). Qed.
Lemma lem3694260 {_93839 : Type'} (P : _93839 -> Prop) : (term72 _93839 P) = (term121 _93839 P).
Proof. exact (TRANS (@lem3694231 _93839 P) (@lem3694258 _93839 P)). Qed.
Lemma lem3694261 {_93839 : Type'} (P : _93839 -> Prop) : (term33 _93839 P) = (term121 _93839 P).
Proof. exact (TRANS (@lem3694167 _93839 P) (@lem3694260 _93839 P)). Qed.
Lemma lem3694262 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : term121 _93839 P.
Proof. exact (EQ_MP (@lem3694261 _93839 P) (@lem3694122 _93839 P h1)). Qed.
Lemma lem3694263 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term118 _93839 x P) : term118 _93839 x P.
Proof. exact (h1). Qed.
Lemma lem3694266 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3694267 {_93839 : Type'} (P : _93839 -> Prop) : (term46 _93839 P) = (term46 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694266 _93839 P x)). Qed.
Lemma lem3694268 {_93839 : Type'} : (@all _93839) = (@all _93839).
Proof. exact (eq_refl (@all _93839)). Qed.
Lemma lem3694269 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term30 _93839 P).
Proof. exact (MK_COMB (@lem3694268 _93839) (@lem3694267 _93839 P)). Qed.
Lemma lem3694276 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term95 _93839 P x) = (term95 _93839 P x).
Proof. exact (eq_refl (term95 _93839 P x)). Qed.
Lemma lem3694277 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) : (term97 _93839 x P) = (term97 _93839 x P).
Proof. exact (MK_COMB (@lem3694276 _93839 P x) (@lem3694269 _93839 P)). Qed.
Lemma lem3694282 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term43 _93839 P x) = (term43 _93839 P x).
Proof. exact (eq_refl (term43 _93839 P x)). Qed.
Lemma lem3694285 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3694286 {_93839 : Type'} (P : _93839 -> Prop) : (term46 _93839 P) = (term46 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694285 _93839 P x)). Qed.
Lemma lem3694287 {_93839 : Type'} : (@all _93839) = (@all _93839).
Proof. exact (eq_refl (@all _93839)). Qed.
Lemma lem3694288 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term30 _93839 P).
Proof. exact (MK_COMB (@lem3694287 _93839) (@lem3694286 _93839 P)). Qed.
Lemma lem3694289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3694290 {_93839 : Type'} (P : _93839 -> Prop) : (term66 _93839 P) = (term66 _93839 P).
Proof. exact (MK_COMB (@lem3694289) (@lem3694288 _93839 P)). Qed.
Lemma lem3694291 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term82 _93839 P x) = (term82 _93839 P x).
Proof. exact (MK_COMB (@lem3694290 _93839 P) (@lem3694282 _93839 P x)). Qed.
Lemma lem3694292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3694293 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term116 _93839 P x) = (term116 _93839 P x).
Proof. exact (MK_COMB (@lem3694292) (@lem3694291 _93839 P x)). Qed.
Lemma lem3694294 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) : (term118 _93839 x P) = (term118 _93839 x P).
Proof. exact (MK_COMB (@lem3694293 _93839 P x) (@lem3694277 _93839 x P)). Qed.
Lemma lem3694295 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term118 _93839 x P) : term118 _93839 x P.
Proof. exact (EQ_MP (@lem3694294 _93839 x P) (@lem3694263 _93839 x P h1)). Qed.
Lemma lem3694296 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : term82 _93839 P x.
Proof. exact (h1). Qed.
Lemma lem3694297 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : term97 _93839 x P.
Proof. exact (h1). Qed.
Lemma lem3694299 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : term30 _93839 P.
Proof. exact (proj1 (@lem3694296 _93839 P x h1)). Qed.
Lemma lem3694300 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : term30 _93839 P.
Proof. exact (proj2 (@lem3694297 _93839 x P h1)). Qed.
Lemma lem3694303 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3694304 {_93839 : Type'} (P : _93839 -> Prop) : (term46 _93839 P) = (term46 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694303 _93839 P x)). Qed.
Lemma lem3694305 {_93839 : Type'} : (@all _93839) = (@all _93839).
Proof. exact (eq_refl (@all _93839)). Qed.
Lemma lem3694307 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term30 _93839 P).
Proof. exact (MK_COMB (@lem3694305 _93839) (@lem3694304 _93839 P)). Qed.
Lemma lem3694308 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : term30 _93839 P.
Proof. exact (EQ_MP (@lem3694307 _93839 P) (@lem3694299 _93839 P x h1)). Qed.
Lemma lem3694318 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3694319 {_93839 : Type'} (P : _93839 -> Prop) : (term46 _93839 P) = (term46 _93839 P).
Proof. exact (fun_ext (fun x : _93839 => @lem3694318 _93839 P x)). Qed.
Lemma lem3694320 {_93839 : Type'} : (@all _93839) = (@all _93839).
Proof. exact (eq_refl (@all _93839)). Qed.
Lemma lem3694322 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term30 _93839 P).
Proof. exact (MK_COMB (@lem3694320 _93839) (@lem3694319 _93839 P)). Qed.
Lemma lem3694323 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : term30 _93839 P.
Proof. exact (EQ_MP (@lem3694322 _93839 P) (@lem3694300 _93839 x P h1)). Qed.
Lemma lem3694324 {_93839 : Type'} (_42487 : _93839) (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : term51 _93839 P _42487.
Proof. exact (@lem3694308 _93839 P x h1 _42487). Qed.
Lemma lem3694325 {_93839 : Type'} (P : _93839 -> Prop) (_42487 : _93839) : (term51 _93839 P _42487) = (P _42487).
Proof. exact (eq_refl (term51 _93839 P _42487)). Qed.
Lemma lem3694327 {_93839 : Type'} (_42488 : _93839) (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : term51 _93839 P _42488.
Proof. exact (@lem3694323 _93839 x P h1 _42488). Qed.
Lemma lem3694328 {_93839 : Type'} (P : _93839 -> Prop) (_42488 : _93839) : (term51 _93839 P _42488) = (P _42488).
Proof. exact (eq_refl (term51 _93839 P _42488)). Qed.
Lemma lem3694333 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : term43 _93839 P x.
Proof. exact (proj2 (@lem3694296 _93839 P x h1)). Qed.
Lemma lem3694335 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : term43 _93839 P x.
Proof. exact (proj1 (@lem3694297 _93839 x P h1)). Qed.
Lemma lem3694339 {_93839 : Type'} (_42487 : _93839) (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : P _42487.
Proof. exact (EQ_MP (@lem3694325 _93839 P _42487) (@lem3694324 _93839 _42487 P x h1)). Qed.
Lemma lem3694340 {_93839 : Type'} (_42487 : _93839) (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : P _42487.
Proof. exact (@lem3694339 _93839 _42487 P x h1). Qed.
Lemma lem3694341 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : P x.
Proof. exact (@lem3694340 _93839 x P x h1). Qed.
Lemma lem3694342 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : term122 _93839 P x.
Proof. exact (fun h0 : term43 _93839 P x => @lem3694341 _93839 P x h1). Qed.
Lemma lem3694344 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3694345 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term122 _93839 P x) = (P x).
Proof. exact (@lem3694344 (P x)). Qed.
Lemma lem3694346 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : P x.
Proof. exact (EQ_MP (@lem3694345 _93839 P x) (@lem3694342 _93839 P x h1)). Qed.
Lemma lem3694349 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3694351 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term43 _93839 P x) = (term124 _93839 P x).
Proof. exact (@lem3694349 (P x)). Qed.
Lemma lem3694354 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : term124 _93839 P x.
Proof. exact (EQ_MP (@lem3694351 _93839 P x) (@lem3694333 _93839 P x h1)). Qed.
Lemma lem3694357 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : False.
Proof. exact (@lem3694354 _93839 P x h1 (@lem3694346 _93839 P x h1)). Qed.
Lemma lem3694358 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : term125.
Proof. exact (fun h0 : ~ False => @lem3694357 _93839 P x h1). Qed.
Lemma lem3694360 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3694361 : term125 = False.
Proof. exact (@lem3694360 False). Qed.
Lemma lem3694362 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) (h1 : term82 _93839 P x) : False.
Proof. exact (EQ_MP (@lem3694361) (@lem3694358 _93839 P x h1)). Qed.
Lemma lem3694364 {_93839 : Type'} (_42488 : _93839) (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : P _42488.
Proof. exact (EQ_MP (@lem3694328 _93839 P _42488) (@lem3694327 _93839 _42488 x P h1)). Qed.
Lemma lem3694365 {_93839 : Type'} (_42488 : _93839) (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : P _42488.
Proof. exact (@lem3694364 _93839 _42488 x P h1). Qed.
Lemma lem3694366 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : P x.
Proof. exact (@lem3694365 _93839 x x P h1). Qed.
Lemma lem3694367 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : term122 _93839 P x.
Proof. exact (fun h0 : term43 _93839 P x => @lem3694366 _93839 x P h1). Qed.
Lemma lem3694369 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3694370 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term122 _93839 P x) = (P x).
Proof. exact (@lem3694369 (P x)). Qed.
Lemma lem3694371 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : P x.
Proof. exact (EQ_MP (@lem3694370 _93839 P x) (@lem3694367 _93839 x P h1)). Qed.
Lemma lem3694374 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3694376 {_93839 : Type'} (P : _93839 -> Prop) (x : _93839) : (term43 _93839 P x) = (term124 _93839 P x).
Proof. exact (@lem3694374 (P x)). Qed.
Lemma lem3694379 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : term124 _93839 P x.
Proof. exact (EQ_MP (@lem3694376 _93839 P x) (@lem3694335 _93839 x P h1)). Qed.
Lemma lem3694382 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : False.
Proof. exact (@lem3694379 _93839 x P h1 (@lem3694371 _93839 x P h1)). Qed.
Lemma lem3694383 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : term125.
Proof. exact (fun h0 : ~ False => @lem3694382 _93839 x P h1). Qed.
Lemma lem3694385 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3694386 : term125 = False.
Proof. exact (@lem3694385 False). Qed.
Lemma lem3694387 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term97 _93839 x P) : False.
Proof. exact (EQ_MP (@lem3694386) (@lem3694383 _93839 x P h1)). Qed.
Lemma lem3694388 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term118 _93839 x P) : False.
Proof. exact (or_elim (@lem3694295 _93839 x P h1) (fun h0 : term82 _93839 P x => @lem3694362 _93839 P x h0) (fun h0 : term97 _93839 x P => @lem3694387 _93839 x P h0)). Qed.
Lemma lem3694389 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term118 _93839 x P) : (term118 _93839 x P) = False.
Proof. exact (prop_ext (fun h2 : term118 _93839 x P => @lem3694388 _93839 x P h1) (fun h2 : False => @lem3694295 _93839 x P h1)). Qed.
Lemma lem3694390 {_93839 : Type'} (x : _93839) (P : _93839 -> Prop) (h1 : term118 _93839 x P) : False.
Proof. exact (EQ_MP (@lem3694389 _93839 x P h1) (@lem3694295 _93839 x P h1)). Qed.
Lemma lem3694391 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : False.
Proof. exact (ex_elim (@lem3694262 _93839 P h1) (fun x : _93839 => fun h0 : term120 _93839 P x => @lem3694390 _93839 x P h0)). Qed.
Lemma lem3694392 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : (term33 _93839 P) = False.
Proof. exact (prop_ext (fun h2 : term33 _93839 P => @lem3694391 _93839 P h1) (fun h2 : False => @lem3694122 _93839 P h1)). Qed.
Lemma lem3694393 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : False.
Proof. exact (EQ_MP (@lem3694392 _93839 P h1) (@lem3694122 _93839 P h1)). Qed.
Lemma lem3694394 {_93839 : Type'} (P : _93839 -> Prop) : term32 _93839 P.
Proof. exact (fun h0 : term33 _93839 P => @lem3694393 _93839 P h0). Qed.
Lemma lem3694395 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term31 _93839 P).
Proof. exact (EQ_MP (@lem3694121 _93839 P) (@lem3694394 _93839 P)). Qed.
Lemma lem3694400 {_93839 : Type'} : term42 _93839.
Proof. exact (fun P : _93839 -> Prop => @lem3694395 _93839 P). Qed.
Lemma lem3694401 {_93839 : Type'} : term41 _93839.
Proof. exact (EQ_MP (@lem3694117 _93839) (@lem3694400 _93839)). Qed.
Lemma lem3694402 {_93839 : Type'} (P : _93839 -> Prop) : term126 _93839 P.
Proof. exact (@lem3694401 _93839 P). Qed.
Lemma lem3694403 {_93839 : Type'} (P : _93839 -> Prop) : (term126 _93839 P) = (term32 _93839 P).
Proof. exact (eq_refl (term126 _93839 P)). Qed.
Lemma lem3694404 {_93839 : Type'} (P : _93839 -> Prop) : term32 _93839 P.
Proof. exact (EQ_MP (@lem3694403 _93839 P) (@lem3694402 _93839 P)). Qed.
Lemma lem3694406 {_93839 : Type'} (P : _93839 -> Prop) : term32 _93839 P.
Proof. exact (@lem3694047 _93839 P (@lem3694404 _93839 P)). Qed.
Lemma lem3694407 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : False.
Proof. exact (@lem3694406 _93839 P (@lem3694031 _93839 P h1)). Qed.
Lemma lem3694408 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : (term33 _93839 P) = False.
Proof. exact (prop_ext (fun h2 : term33 _93839 P => @lem3694407 _93839 P h1) (fun h2 : False => @lem3694031 _93839 P h1)). Qed.
Lemma lem3694409 {_93839 : Type'} (P : _93839 -> Prop) (h1 : term33 _93839 P) : False.
Proof. exact (EQ_MP (@lem3694408 _93839 P h1) (@lem3694031 _93839 P h1)). Qed.
Lemma lem3694410 {_93839 : Type'} (P : _93839 -> Prop) : term32 _93839 P.
Proof. exact (fun h0 : term33 _93839 P => @lem3694409 _93839 P h0). Qed.
Lemma lem3694419 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term31 _93839 P).
Proof. exact (EQ_MP (@lem3694030 _93839 P) (@lem3694410 _93839 P)). Qed.
Lemma lem3694420 {_93890 : Type'} (P : type686 _93890) : (term127 _93890 P) = (term128 _93890 P).
Proof. exact (@lem3694419 (_93890 -> Prop) P). Qed.
Lemma lem3694421 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term129 _93870 _93890 f s P) = (term130 _93870 _93890 f s P).
Proof. exact (@lem3694420 _93890 (term131 _93870 _93890 f s P)). Qed.
Lemma lem3694422 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) (t : _93890 -> Prop) : (term132 _93870 _93890 f s P t) = (term133 _93870 _93890 f s P t).
Proof. exact (eq_refl (term132 _93870 _93890 f s P t)). Qed.
Lemma lem3694423 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term134 _93870 _93890 f s P) = (term131 _93870 _93890 f s P).
Proof. exact (fun_ext (fun t : _93890 -> Prop => @lem3694422 _93870 _93890 f s P t)). Qed.
Lemma lem3694424 {_93890 : Type'} : (@all (_93890 -> Prop)) = (@all (_93890 -> Prop)).
Proof. exact (eq_refl (@all (_93890 -> Prop))). Qed.
Lemma lem3694425 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term129 _93870 _93890 f s P) = (term135 _93870 _93890 f s P).
Proof. exact (MK_COMB (@lem3694424 _93890) (@lem3694423 _93870 _93890 f s P)). Qed.
Lemma lem3694426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694427 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term136 _93870 _93890 f s P) = (term137 _93870 _93890 f s P).
Proof. exact (MK_COMB (@lem3694426) (@lem3694425 _93870 _93890 f s P)). Qed.
Lemma lem3694428 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) (t : _93890 -> Prop) : (term132 _93870 _93890 f s P t) = (term133 _93870 _93890 f s P t).
Proof. exact (eq_refl (term132 _93870 _93890 f s P t)). Qed.
Lemma lem3694429 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694430 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) (t : _93890 -> Prop) : (term138 _93870 _93890 f s P t) = (term139 _93870 _93890 f s P t).
Proof. exact (MK_COMB (@lem3694429) (@lem3694428 _93870 _93890 f s P t)). Qed.
Lemma lem3694431 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term140 _93870 _93890 f s P) = (term141 _93870 _93890 f s P).
Proof. exact (fun_ext (fun t : _93890 -> Prop => @lem3694430 _93870 _93890 f s P t)). Qed.
Lemma lem3694432 {_93890 : Type'} : (@ex (_93890 -> Prop)) = (@ex (_93890 -> Prop)).
Proof. exact (eq_refl (@ex (_93890 -> Prop))). Qed.
Lemma lem3694433 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term142 _93870 _93890 f s P) = (term143 _93870 _93890 f s P).
Proof. exact (MK_COMB (@lem3694432 _93890) (@lem3694431 _93870 _93890 f s P)). Qed.
Lemma lem3694434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694435 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term130 _93870 _93890 f s P) = (term144 _93870 _93890 f s P).
Proof. exact (MK_COMB (@lem3694434) (@lem3694433 _93870 _93890 f s P)). Qed.
Lemma lem3694436 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : ((term129 _93870 _93890 f s P) = (term130 _93870 _93890 f s P)) = ((term135 _93870 _93890 f s P) = (term144 _93870 _93890 f s P)).
Proof. exact (MK_COMB (@lem3694427 _93870 _93890 f s P) (@lem3694435 _93870 _93890 f s P)). Qed.
Lemma lem3694437 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term135 _93870 _93890 f s P) = (term144 _93870 _93890 f s P).
Proof. exact (EQ_MP (@lem3694436 _93870 _93890 f s P) (@lem3694421 _93870 _93890 f s P)). Qed.
Lemma lem3694438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694439 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term137 _93870 _93890 f s P) = (term145 _93870 _93890 f s P).
Proof. exact (MK_COMB (@lem3694438) (@lem3694437 _93870 _93890 f s P)). Qed.
Lemma lem3694445 {_93839 : Type'} (P : _93839 -> Prop) : (term30 _93839 P) = (term31 _93839 P).
Proof. exact (EQ_MP (@lem3694030 _93839 P) (@lem3694410 _93839 P)). Qed.
Lemma lem3694446 {_93870 : Type'} (P : type686 _93870) : (term127 _93870 P) = (term128 _93870 P).
Proof. exact (@lem3694445 (_93870 -> Prop) P). Qed.
Lemma lem3694447 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term146 _93870 _93890 s P f) = (term147 _93870 _93890 s P f).
Proof. exact (@lem3694446 _93870 (term148 _93870 _93890 s P f)). Qed.
Lemma lem3694448 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term149 _93870 _93890 s P f t) = (term150 _93870 _93890 s P f t).
Proof. exact (eq_refl (term149 _93870 _93890 s P f t)). Qed.
Lemma lem3694449 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term151 _93870 _93890 s P f) = (term148 _93870 _93890 s P f).
Proof. exact (fun_ext (fun t : _93870 -> Prop => @lem3694448 _93870 _93890 s P f t)). Qed.
Lemma lem3694450 {_93870 : Type'} : (@all (_93870 -> Prop)) = (@all (_93870 -> Prop)).
Proof. exact (eq_refl (@all (_93870 -> Prop))). Qed.
Lemma lem3694451 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term146 _93870 _93890 s P f) = (term152 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694450 _93870) (@lem3694449 _93870 _93890 s P f)). Qed.
Lemma lem3694452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694453 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term153 _93870 _93890 s P f) = (term154 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694452) (@lem3694451 _93870 _93890 s P f)). Qed.
Lemma lem3694454 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term149 _93870 _93890 s P f t) = (term150 _93870 _93890 s P f t).
Proof. exact (eq_refl (term149 _93870 _93890 s P f t)). Qed.
Lemma lem3694455 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694456 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term155 _93870 _93890 s P f t) = (term156 _93870 _93890 s P f t).
Proof. exact (MK_COMB (@lem3694455) (@lem3694454 _93870 _93890 s P f t)). Qed.
Lemma lem3694457 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term157 _93870 _93890 s P f) = (term158 _93870 _93890 s P f).
Proof. exact (fun_ext (fun t : _93870 -> Prop => @lem3694456 _93870 _93890 s P f t)). Qed.
Lemma lem3694458 {_93870 : Type'} : (@ex (_93870 -> Prop)) = (@ex (_93870 -> Prop)).
Proof. exact (eq_refl (@ex (_93870 -> Prop))). Qed.
Lemma lem3694459 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term159 _93870 _93890 s P f) = (term160 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694458 _93870) (@lem3694457 _93870 _93890 s P f)). Qed.
Lemma lem3694460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694461 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term147 _93870 _93890 s P f) = (term161 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694460) (@lem3694459 _93870 _93890 s P f)). Qed.
Lemma lem3694462 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : ((term146 _93870 _93890 s P f) = (term147 _93870 _93890 s P f)) = ((term152 _93870 _93890 s P f) = (term161 _93870 _93890 s P f)).
Proof. exact (MK_COMB (@lem3694453 _93870 _93890 s P f) (@lem3694461 _93870 _93890 s P f)). Qed.
Lemma lem3694463 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term152 _93870 _93890 s P f) = (term161 _93870 _93890 s P f).
Proof. exact (EQ_MP (@lem3694462 _93870 _93890 s P f) (@lem3694447 _93870 _93890 s P f)). Qed.
Lemma lem3694464 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : ((term135 _93870 _93890 f s P) = (term152 _93870 _93890 s P f)) = ((term144 _93870 _93890 f s P) = (term161 _93870 _93890 s P f)).
Proof. exact (MK_COMB (@lem3694439 _93870 _93890 f s P) (@lem3694463 _93870 _93890 s P f)). Qed.
Lemma lem3694465 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : ((term144 _93870 _93890 f s P) = (term161 _93870 _93890 s P f)) = ((term135 _93870 _93890 f s P) = (term152 _93870 _93890 s P f)).
Proof. exact (SYM (@lem3694464 _93870 _93890 s P f)). Qed.
Lemma lem3694473 (t1 : Prop) (t2 : Prop) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (EQ_MP (@lem3694015 t1 t2) (@lem3694014 t1 t2)). Qed.
Lemma lem3694474 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) (t : _93890 -> Prop) : (term139 _93870 _93890 f s P t) = (term162 _93870 _93890 f s P t).
Proof. exact (@lem3694473 (term163 _93870 _93890 t f s) (P t)). Qed.
Lemma lem3694476 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem3694009 t1 t2 t3) (@lem3694008 t1 t2 t3)). Qed.
Lemma lem3694477 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) (t : _93890 -> Prop) : (term162 _93870 _93890 f s P t) = (term164 _93870 _93890 f s P t).
Proof. exact (@lem3694476 (@FINITE _93890 t) (term165 _93870 _93890 t f s) (term166 _93890 P t)). Qed.
Lemma lem3694480 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) (t : _93890 -> Prop) : (term139 _93870 _93890 f s P t) = (term164 _93870 _93890 f s P t).
Proof. exact (TRANS (@lem3694474 _93870 _93890 f s P t) (@lem3694477 _93870 _93890 f s P t)). Qed.
Lemma lem3694483 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term141 _93870 _93890 f s P) = (term167 _93870 _93890 f s P).
Proof. exact (fun_ext (fun t : _93890 -> Prop => @lem3694480 _93870 _93890 f s P t)). Qed.
Lemma lem3694484 {_93890 : Type'} : (@ex (_93890 -> Prop)) = (@ex (_93890 -> Prop)).
Proof. exact (eq_refl (@ex (_93890 -> Prop))). Qed.
Lemma lem3694485 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term143 _93870 _93890 f s P) = (term168 _93870 _93890 f s P).
Proof. exact (MK_COMB (@lem3694484 _93890) (@lem3694483 _93870 _93890 f s P)). Qed.
Lemma lem3694487 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term19 _93804 _93824 f s P) = (term20 _93804 _93824 s P f).
Proof. exact (EQ_MP (@lem3694000 _93804 _93824 s P f) (@lem3693999 _93804 _93824 P f s)). Qed.
Lemma lem3694488 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term19 _93870 _93890 f s P) = (term20 _93870 _93890 s P f).
Proof. exact (@lem3694487 _93870 _93890 s P f). Qed.
Lemma lem3694489 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term169 _93870 _93890 f s P) = (term170 _93870 _93890 s P f).
Proof. exact (@lem3694488 _93870 _93890 s (term171 _93890 P) f). Qed.
Lemma lem3694490 {_93890 : Type'} (P : type686 _93890) (t : _93890 -> Prop) : (term172 _93890 P t) = (term166 _93890 P t).
Proof. exact (eq_refl (term172 _93890 P t)). Qed.
Lemma lem3694491 {_93870 _93890 : Type'} (t : _93890 -> Prop) (f : _93870 -> _93890) (s : _93870 -> Prop) : (term173 _93870 _93890 t f s) = (term173 _93870 _93890 t f s).
Proof. exact (eq_refl (term173 _93870 _93890 t f s)). Qed.
Lemma lem3694492 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) (t : _93890 -> Prop) : (term174 _93870 _93890 f s P t) = (term175 _93870 _93890 f s P t).
Proof. exact (MK_COMB (@lem3694491 _93870 _93890 t f s) (@lem3694490 _93890 P t)). Qed.
Lemma lem3694493 {_93890 : Type'} (t : _93890 -> Prop) : (term176 _93890 t) = (term176 _93890 t).
Proof. exact (eq_refl (term176 _93890 t)). Qed.
Lemma lem3694494 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) (t : _93890 -> Prop) : (term177 _93870 _93890 f s P t) = (term164 _93870 _93890 f s P t).
Proof. exact (MK_COMB (@lem3694493 _93890 t) (@lem3694492 _93870 _93890 f s P t)). Qed.
Lemma lem3694495 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term178 _93870 _93890 f s P) = (term167 _93870 _93890 f s P).
Proof. exact (fun_ext (fun t : _93890 -> Prop => @lem3694494 _93870 _93890 f s P t)). Qed.
Lemma lem3694496 {_93890 : Type'} : (@ex (_93890 -> Prop)) = (@ex (_93890 -> Prop)).
Proof. exact (eq_refl (@ex (_93890 -> Prop))). Qed.
Lemma lem3694497 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term169 _93870 _93890 f s P) = (term168 _93870 _93890 f s P).
Proof. exact (MK_COMB (@lem3694496 _93890) (@lem3694495 _93870 _93890 f s P)). Qed.
Lemma lem3694498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694499 {_93870 _93890 : Type'} (f : _93870 -> _93890) (s : _93870 -> Prop) (P : type686 _93890) : (term179 _93870 _93890 f s P) = (term180 _93870 _93890 f s P).
Proof. exact (MK_COMB (@lem3694498) (@lem3694497 _93870 _93890 f s P)). Qed.
Lemma lem3694500 {_93870 _93890 : Type'} (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term181 _93870 _93890 P f t) = (term182 _93870 _93890 P f t).
Proof. exact (eq_refl (term181 _93870 _93890 P f t)). Qed.
Lemma lem3694501 {_93870 : Type'} (t : _93870 -> Prop) (s : _93870 -> Prop) : (term183 _93870 t s) = (term183 _93870 t s).
Proof. exact (eq_refl (term183 _93870 t s)). Qed.
Lemma lem3694502 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term184 _93870 _93890 s P f t) = (term185 _93870 _93890 s P f t).
Proof. exact (MK_COMB (@lem3694501 _93870 t s) (@lem3694500 _93870 _93890 P f t)). Qed.
Lemma lem3694503 {_93870 : Type'} (t : _93870 -> Prop) : (term176 _93870 t) = (term176 _93870 t).
Proof. exact (eq_refl (term176 _93870 t)). Qed.
Lemma lem3694504 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term186 _93870 _93890 s P f t) = (term187 _93870 _93890 s P f t).
Proof. exact (MK_COMB (@lem3694503 _93870 t) (@lem3694502 _93870 _93890 s P f t)). Qed.
Lemma lem3694505 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term188 _93870 _93890 s P f) = (term189 _93870 _93890 s P f).
Proof. exact (fun_ext (fun t : _93870 -> Prop => @lem3694504 _93870 _93890 s P f t)). Qed.
Lemma lem3694506 {_93870 : Type'} : (@ex (_93870 -> Prop)) = (@ex (_93870 -> Prop)).
Proof. exact (eq_refl (@ex (_93870 -> Prop))). Qed.
Lemma lem3694507 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term170 _93870 _93890 s P f) = (term190 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694506 _93870) (@lem3694505 _93870 _93890 s P f)). Qed.
Lemma lem3694508 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : ((term169 _93870 _93890 f s P) = (term170 _93870 _93890 s P f)) = ((term168 _93870 _93890 f s P) = (term190 _93870 _93890 s P f)).
Proof. exact (MK_COMB (@lem3694499 _93870 _93890 f s P) (@lem3694507 _93870 _93890 s P f)). Qed.
Lemma lem3694509 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term168 _93870 _93890 f s P) = (term190 _93870 _93890 s P f).
Proof. exact (EQ_MP (@lem3694508 _93870 _93890 s P f) (@lem3694489 _93870 _93890 s P f)). Qed.
Lemma lem3694518 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term143 _93870 _93890 f s P) = (term190 _93870 _93890 s P f).
Proof. exact (TRANS (@lem3694485 _93870 _93890 f s P) (@lem3694509 _93870 _93890 s P f)). Qed.
Lemma lem3694519 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694520 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term144 _93870 _93890 f s P) = (term191 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694519) (@lem3694518 _93870 _93890 s P f)). Qed.
Lemma lem3694521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3694522 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term145 _93870 _93890 f s P) = (term192 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694521) (@lem3694520 _93870 _93890 s P f)). Qed.
Lemma lem3694528 (t1 : Prop) (t2 : Prop) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (EQ_MP (@lem3694015 t1 t2) (@lem3694014 t1 t2)). Qed.
Lemma lem3694529 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term156 _93870 _93890 s P f t) = (term193 _93870 _93890 s P f t).
Proof. exact (@lem3694528 (term194 _93870 t s) (term195 _93870 _93890 P f t)). Qed.
Lemma lem3694531 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem3694009 t1 t2 t3) (@lem3694008 t1 t2 t3)). Qed.
Lemma lem3694532 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term193 _93870 _93890 s P f t) = (term187 _93870 _93890 s P f t).
Proof. exact (@lem3694531 (@FINITE _93870 t) (@SUBSET _93870 t s) (term182 _93870 _93890 P f t)). Qed.
Lemma lem3694535 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) (t : _93870 -> Prop) : (term156 _93870 _93890 s P f t) = (term187 _93870 _93890 s P f t).
Proof. exact (TRANS (@lem3694529 _93870 _93890 s P f t) (@lem3694532 _93870 _93890 s P f t)). Qed.
Lemma lem3694538 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term158 _93870 _93890 s P f) = (term189 _93870 _93890 s P f).
Proof. exact (fun_ext (fun t : _93870 -> Prop => @lem3694535 _93870 _93890 s P f t)). Qed.
Lemma lem3694539 {_93870 : Type'} : (@ex (_93870 -> Prop)) = (@ex (_93870 -> Prop)).
Proof. exact (eq_refl (@ex (_93870 -> Prop))). Qed.
Lemma lem3694540 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term160 _93870 _93890 s P f) = (term190 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694539 _93870) (@lem3694538 _93870 _93890 s P f)). Qed.
Lemma lem3694545 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694546 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term161 _93870 _93890 s P f) = (term191 _93870 _93890 s P f).
Proof. exact (MK_COMB (@lem3694545) (@lem3694540 _93870 _93890 s P f)). Qed.
Lemma lem3694547 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : ((term144 _93870 _93890 f s P) = (term161 _93870 _93890 s P f)) = ((term191 _93870 _93890 s P f) = (term191 _93870 _93890 s P f)).
Proof. exact (MK_COMB (@lem3694522 _93870 _93890 s P f) (@lem3694546 _93870 _93890 s P f)). Qed.
Lemma lem3694549 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3694550 (x : Prop) : (x = x) = True.
Proof. exact (@lem3694549 Prop x). Qed.
Lemma lem3694551 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : ((term191 _93870 _93890 s P f) = (term191 _93870 _93890 s P f)) = True.
Proof. exact (@lem3694550 (term191 _93870 _93890 s P f)). Qed.
Lemma lem3694552 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : ((term144 _93870 _93890 f s P) = (term161 _93870 _93890 s P f)) = True.
Proof. exact (TRANS (@lem3694547 _93870 _93890 s P f) (@lem3694551 _93870 _93890 s P f)). Qed.
Lemma lem3694553 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : True = ((term144 _93870 _93890 f s P) = (term161 _93870 _93890 s P f)).
Proof. exact (SYM (@lem3694552 _93870 _93890 s P f)). Qed.
Lemma lem3694554 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term144 _93870 _93890 f s P) = (term161 _93870 _93890 s P f).
Proof. exact (EQ_MP (@lem3694553 _93870 _93890 s P f) (@lem0)). Qed.
Lemma lem3694555 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term135 _93870 _93890 f s P) = (term152 _93870 _93890 s P f).
Proof. exact (EQ_MP (@lem3694465 _93870 _93890 s P f) (@lem3694554 _93870 _93890 s P f)). Qed.
Lemma lem3694560 {_93870 _93890 : Type'} (P : type686 _93890) (f : _93870 -> _93890) : term196 _93870 _93890 P f.
Proof. exact (fun s : _93870 -> Prop => @lem3694555 _93870 _93890 s P f). Qed.
Lemma lem3694565 {_93870 _93890 : Type'} (P : type686 _93890) : term197 _93870 _93890 P.
Proof. exact (fun f : _93870 -> _93890 => @lem3694560 _93870 _93890 P f). Qed.
Lemma lem3694570 {_93870 _93890 : Type'} : term198 _93870 _93890.
Proof. exact (fun P : type686 _93890 => @lem3694565 _93870 _93890 P). Qed.
