Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_OF_INTER_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_UNION_OF_INC_spec.
Require Import FINITE_UNION_OF_INTER_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4889828 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4889829 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4889830 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4889829 t1) (@lem4889828 t1)). Qed.
Lemma lem4889831 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4889830 t1 t2). Qed.
Lemma lem4889832 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4889833 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4889832 t1 t2) (@lem4889831 t1 t2)). Qed.
Lemma lem4889834 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4889833 t1 t2 t3). Qed.
Lemma lem4889835 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4889836 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4889835 t1 t2 t3) (@lem4889834 t1 t2 t3)). Qed.
Lemma lem4889837 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4889836 t1 t2 t3)). Qed.
Lemma lem4889838 {A : Type'} (P : type686 A) : term7 A P.
Proof. exact (@lem4889827 A P). Qed.
Lemma lem4889839 {A : Type'} (P : type686 A) : (term7 A P) = ((term8 A P) = (term9 A P)).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem4889860 {A : Type'} (P : type686 A) : (term8 A P) = (term9 A P).
Proof. exact (EQ_MP (@lem4889839 A P) (@lem4889838 A P)). Qed.
Lemma lem4889861 {A : Type'} (P : type686 A) : (term8 A P) = (term9 A P).
Proof. exact (@lem4889860 A P). Qed.
Lemma lem4889874 {A : Type'} (P : type686 A) : (term10 A P) = (term10 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem4889875 {A : Type'} (P : type686 A) : (term11 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem4889874 A P) (@lem4889861 A P)). Qed.
Lemma lem4889878 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4889875 A P)). Qed.
Lemma lem4889879 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4889880 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem4889879 A) (@lem4889878 A)). Qed.
Lemma lem4889885 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem4889880 A)). Qed.
Lemma lem4889887 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4889888 {A : Type'} : (term16 A) = (term18 A).
Proof. exact (@lem4889887 (term16 A)). Qed.
Lemma lem4889889 {A : Type'} : (term18 A) = (term16 A).
Proof. exact (SYM (@lem4889888 A)). Qed.
Lemma lem4889890 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem4889891 {A : Type'} : term20 A.
Proof. exact (@lem4876798 A). Qed.
Lemma lem4889895 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem4889896 {A : Type'} : term22 A.
Proof. exact (fun h0 : term21 A => @lem4889895 A h0). Qed.
Lemma lem4889897 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem4889898 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem4889899 {A : Type'} (h1 : term21 A) (h2 : term22 A) : term21 A.
Proof. exact (@lem4889897 A h2 (@lem4889898 A h1)). Qed.
Lemma lem4889900 {A : Type'} (h1 : term21 A) : term23 A.
Proof. exact (fun h0 : term22 A => @lem4889899 A h1 h0). Qed.
Lemma lem4889901 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem4889902 {A : Type'} (h1 : term21 A) (h2 : term22 A) : term21 A.
Proof. exact (@lem4889900 A h1 (@lem4889901 A h2)). Qed.
Lemma lem4889903 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (fun h0 : term21 A => @lem4889902 A h0 h1). Qed.
Lemma lem4889904 {A : Type'} : term24 A.
Proof. exact (fun h0 : term22 A => @lem4889903 A h0). Qed.
Lemma lem4889907 {A : Type'} : term22 A.
Proof. exact (@lem4889904 A (@lem4889896 A)). Qed.
Lemma lem4889908 {A : Type'} : term22 A.
Proof. exact (@lem4889907 A). Qed.
Lemma lem4889942 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4889943 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem4889942 (term20 A)). Qed.
Lemma lem4889954 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (eq_refl (term27 A)). Qed.
Lemma lem4889961 {A : Type'} : (term21 A) = (term28 A).
Proof. exact (MK_COMB (@lem4889954 A) (@lem4889943 A)). Qed.
Lemma lem4889966 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term29 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4889967 {A : Type'} (P : type686 A) : (term30 A P) = (term30 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4889966 A P s)). Qed.
Lemma lem4889968 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889969 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4889968 A) (@lem4889967 A P)). Qed.
Lemma lem4889970 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4889969 A P)). Qed.
Lemma lem4889971 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4889972 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem4889971 A) (@lem4889970 A)). Qed.
Lemma lem4889973 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4889974 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem4889973) (@lem4889972 A)). Qed.
Lemma lem4889983 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term33 A P s t) = (term33 A P s t).
Proof. exact (eq_refl (term33 A P s t)). Qed.
Lemma lem4889984 {A : Type'} (P : type686 A) (s : A -> Prop) : (term34 A P s) = (term34 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4889983 A P s t)). Qed.
Lemma lem4889985 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889986 {A : Type'} (P : type686 A) (s : A -> Prop) : (term35 A P s) = (term35 A P s).
Proof. exact (MK_COMB (@lem4889985 A) (@lem4889984 A P s)). Qed.
Lemma lem4889987 {A : Type'} (P : type686 A) : (term36 A P) = (term36 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4889986 A P s)). Qed.
Lemma lem4889988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889989 {A : Type'} (P : type686 A) : (term9 A P) = (term9 A P).
Proof. exact (MK_COMB (@lem4889988 A) (@lem4889987 A P)). Qed.
Lemma lem4889998 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term37 A P s t).
Proof. exact (eq_refl (term37 A P s t)). Qed.
Lemma lem4889999 {A : Type'} (P : type686 A) (s : A -> Prop) : (term38 A P s) = (term38 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4889998 A P s t)). Qed.
Lemma lem4890000 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890001 {A : Type'} (P : type686 A) (s : A -> Prop) : (term39 A P s) = (term39 A P s).
Proof. exact (MK_COMB (@lem4890000 A) (@lem4889999 A P s)). Qed.
Lemma lem4890002 {A : Type'} (P : type686 A) : (term40 A P) = (term40 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890001 A P s)). Qed.
Lemma lem4890003 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890004 {A : Type'} (P : type686 A) : (term41 A P) = (term41 A P).
Proof. exact (MK_COMB (@lem4890003 A) (@lem4890002 A P)). Qed.
Lemma lem4890005 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4890006 {A : Type'} (P : type686 A) : (term10 A P) = (term10 A P).
Proof. exact (MK_COMB (@lem4890005) (@lem4890004 A P)). Qed.
Lemma lem4890007 {A : Type'} (P : type686 A) : (term12 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem4890006 A P) (@lem4889989 A P)). Qed.
Lemma lem4890008 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4890007 A P)). Qed.
Lemma lem4890009 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4890010 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4890009 A) (@lem4890008 A)). Qed.
Lemma lem4890011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890012 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem4890011) (@lem4890010 A)). Qed.
Lemma lem4890013 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4890014 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem4890013) (@lem4890012 A)). Qed.
Lemma lem4890015 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem4890014 A) (@lem4889974 A)). Qed.
Lemma lem4890074 {A : Type'} : (term21 A) = (term28 A).
Proof. exact (TRANS (@lem4889961 A) (@lem4890015 A)). Qed.
Lemma lem4890075 {A : Type'} : (term28 A) = (term21 A).
Proof. exact (SYM (@lem4890074 A)). Qed.
Lemma lem4890076 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem4890077 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (h1). Qed.
Lemma lem4890084 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term42 A s P t) = (term43 A s P t).
Proof. exact (@lem17045 (P s) (P t)). Qed.
Lemma lem4890085 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term44 A P s t).
Proof. exact (eq_refl (term44 A P s t)). Qed.
Lemma lem4890086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4890087 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term45 A s P t) = (term46 A s P t).
Proof. exact (MK_COMB (@lem4890086) (@lem4890084 A s P t)). Qed.
Lemma lem4890088 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term47 A P s t) = (term48 A P s t).
Proof. exact (MK_COMB (@lem4890087 A s P t) (@lem4890085 A P s t)). Qed.
Lemma lem4890089 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term47 A P s t).
Proof. exact (@lem17265 (term49 A s P t) (term44 A P s t)). Qed.
Lemma lem4890090 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term48 A P s t).
Proof. exact (TRANS (@lem4890089 A P s t) (@lem4890088 A P s t)). Qed.
Lemma lem4890091 {A : Type'} (P : type686 A) (s : A -> Prop) : (term38 A P s) = (term50 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4890090 A P s t)). Qed.
Lemma lem4890092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890093 {A : Type'} (P : type686 A) (s : A -> Prop) : (term39 A P s) = (term51 A P s).
Proof. exact (MK_COMB (@lem4890092 A) (@lem4890091 A P s)). Qed.
Lemma lem4890094 {A : Type'} (P : type686 A) : (term40 A P) = (term52 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890093 A P s)). Qed.
Lemma lem4890095 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890096 {A : Type'} (P : type686 A) : (term41 A P) = (term53 A P).
Proof. exact (MK_COMB (@lem4890095 A) (@lem4890094 A P)). Qed.
Lemma lem4890107 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term55 A P s t).
Proof. exact (@lem17362 (term49 A s P t) (term56 A P s t)). Qed.
Lemma lem4890108 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4890109 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term60 A P s).
Proof. exact (@lem4890108 A (term34 A P s)). Qed.
Lemma lem4890110 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term61 A P s t) = (term33 A P s t).
Proof. exact (eq_refl (term61 A P s t)). Qed.
Lemma lem4890111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890112 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A P s t) = (term54 A P s t).
Proof. exact (MK_COMB (@lem4890111) (@lem4890110 A P s t)). Qed.
Lemma lem4890113 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A P s t) = (term55 A P s t).
Proof. exact (TRANS (@lem4890112 A P s t) (@lem4890107 A P s t)). Qed.
Lemma lem4890114 {A : Type'} (P : type686 A) (s : A -> Prop) : (term63 A P s) = (term64 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4890113 A P s t)). Qed.
Lemma lem4890115 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4890116 {A : Type'} (P : type686 A) (s : A -> Prop) : (term60 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4890115 A) (@lem4890114 A P s)). Qed.
Lemma lem4890117 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term65 A P s).
Proof. exact (TRANS (@lem4890109 A P s) (@lem4890116 A P s)). Qed.
Lemma lem4890118 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4890119 {A : Type'} (P : type686 A) : (term66 A P) = (term67 A P).
Proof. exact (@lem4890118 A (term36 A P)). Qed.
Lemma lem4890120 {A : Type'} (P : type686 A) (s : A -> Prop) : (term68 A P s) = (term35 A P s).
Proof. exact (eq_refl (term68 A P s)). Qed.
Lemma lem4890121 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890122 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term59 A P s).
Proof. exact (MK_COMB (@lem4890121) (@lem4890120 A P s)). Qed.
Lemma lem4890123 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term65 A P s).
Proof. exact (TRANS (@lem4890122 A P s) (@lem4890117 A P s)). Qed.
Lemma lem4890124 {A : Type'} (P : type686 A) : (term70 A P) = (term71 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890123 A P s)). Qed.
Lemma lem4890125 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4890126 {A : Type'} (P : type686 A) : (term67 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem4890125 A) (@lem4890124 A P)). Qed.
Lemma lem4890127 {A : Type'} (P : type686 A) : (term66 A P) = (term72 A P).
Proof. exact (TRANS (@lem4890119 A P) (@lem4890126 A P)). Qed.
Lemma lem4890128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4890129 {A : Type'} (P : type686 A) : (term73 A P) = (term74 A P).
Proof. exact (MK_COMB (@lem4890128) (@lem4890096 A P)). Qed.
Lemma lem4890130 {A : Type'} (P : type686 A) : (term75 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem4890129 A P) (@lem4890127 A P)). Qed.
Lemma lem4890131 {A : Type'} (P : type686 A) : (term77 A P) = (term75 A P).
Proof. exact (@lem17362 (term41 A P) (term9 A P)). Qed.
Lemma lem4890132 {A : Type'} (P : type686 A) : (term77 A P) = (term76 A P).
Proof. exact (TRANS (@lem4890131 A P) (@lem4890130 A P)). Qed.
Lemma lem4890133 {A : Type'} (P : type180 A) : (term78 A P) = (term79 A P).
Proof. exact (@lem18392 (type686 A) P). Qed.
Lemma lem4890134 {A : Type'} : (term19 A) = (term80 A).
Proof. exact (@lem4890133 A (term14 A)). Qed.
Lemma lem4890135 {A : Type'} (P : type686 A) : (term81 A P) = (term12 A P).
Proof. exact (eq_refl (term81 A P)). Qed.
Lemma lem4890136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890137 {A : Type'} (P : type686 A) : (term82 A P) = (term77 A P).
Proof. exact (MK_COMB (@lem4890136) (@lem4890135 A P)). Qed.
Lemma lem4890138 {A : Type'} (P : type686 A) : (term82 A P) = (term76 A P).
Proof. exact (TRANS (@lem4890137 A P) (@lem4890132 A P)). Qed.
Lemma lem4890139 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4890138 A P)). Qed.
Lemma lem4890140 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4890141 {A : Type'} : (term80 A) = (term85 A).
Proof. exact (MK_COMB (@lem4890140 A) (@lem4890139 A)). Qed.
Lemma lem4890142 {A : Type'} : (term19 A) = (term85 A).
Proof. exact (TRANS (@lem4890134 A) (@lem4890141 A)). Qed.
Lemma lem4890297 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4890298 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem4890297 (A -> Prop) P Q). Qed.
Lemma lem4890299 {A : Type'} (P : type686 A) : (term90 A P) = (term91 A P).
Proof. exact (@lem4890298 A (term53 A P) (term71 A P)). Qed.
Lemma lem4890300 {A : Type'} (P : type686 A) (s : A -> Prop) : (term92 A P s) = (term65 A P s).
Proof. exact (eq_refl (term92 A P s)). Qed.
Lemma lem4890301 {A : Type'} (P : type686 A) : (term93 A P) = (term71 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890300 A P s)). Qed.
Lemma lem4890302 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4890303 {A : Type'} (P : type686 A) : (term94 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem4890302 A) (@lem4890301 A P)). Qed.
Lemma lem4890304 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4890305 {A : Type'} (P : type686 A) : (term90 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem4890304 A P) (@lem4890303 A P)). Qed.
Lemma lem4890306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4890307 {A : Type'} (P : type686 A) : (term95 A P) = (term96 A P).
Proof. exact (MK_COMB (@lem4890306) (@lem4890305 A P)). Qed.
Lemma lem4890308 {A : Type'} (P : type686 A) (s : A -> Prop) : (term92 A P s) = (term65 A P s).
Proof. exact (eq_refl (term92 A P s)). Qed.
Lemma lem4890309 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4890310 {A : Type'} (P : type686 A) (s : A -> Prop) : (term97 A P s) = (term98 A P s).
Proof. exact (MK_COMB (@lem4890309 A P) (@lem4890308 A P s)). Qed.
Lemma lem4890311 {A : Type'} (P : type686 A) : (term99 A P) = (term100 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890310 A P s)). Qed.
Lemma lem4890312 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4890313 {A : Type'} (P : type686 A) : (term91 A P) = (term101 A P).
Proof. exact (MK_COMB (@lem4890312 A) (@lem4890311 A P)). Qed.
Lemma lem4890314 {A : Type'} (P : type686 A) : ((term90 A P) = (term91 A P)) = ((term76 A P) = (term101 A P)).
Proof. exact (MK_COMB (@lem4890307 A P) (@lem4890313 A P)). Qed.
Lemma lem4890315 {A : Type'} (P : type686 A) : (term76 A P) = (term101 A P).
Proof. exact (EQ_MP (@lem4890314 A P) (@lem4890299 A P)). Qed.
Lemma lem4890317 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4890318 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem4890317 (A -> Prop) P Q). Qed.
Lemma lem4890319 {A : Type'} (P : type686 A) (s : A -> Prop) : (term102 A P s) = (term103 A P s).
Proof. exact (@lem4890318 A (term53 A P) (term64 A P s)). Qed.
Lemma lem4890320 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term104 A P s t) = (term55 A P s t).
Proof. exact (eq_refl (term104 A P s t)). Qed.
Lemma lem4890321 {A : Type'} (P : type686 A) (s : A -> Prop) : (term105 A P s) = (term64 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4890320 A P s t)). Qed.
Lemma lem4890322 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4890323 {A : Type'} (P : type686 A) (s : A -> Prop) : (term106 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4890322 A) (@lem4890321 A P s)). Qed.
Lemma lem4890324 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4890325 {A : Type'} (P : type686 A) (s : A -> Prop) : (term102 A P s) = (term98 A P s).
Proof. exact (MK_COMB (@lem4890324 A P) (@lem4890323 A P s)). Qed.
Lemma lem4890326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4890327 {A : Type'} (P : type686 A) (s : A -> Prop) : (term107 A P s) = (term108 A P s).
Proof. exact (MK_COMB (@lem4890326) (@lem4890325 A P s)). Qed.
Lemma lem4890328 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term104 A P s t) = (term55 A P s t).
Proof. exact (eq_refl (term104 A P s t)). Qed.
Lemma lem4890329 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4890330 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term109 A P s t) = (term110 A P s t).
Proof. exact (MK_COMB (@lem4890329 A P) (@lem4890328 A P s t)). Qed.
Lemma lem4890331 {A : Type'} (P : type686 A) (s : A -> Prop) : (term111 A P s) = (term112 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4890330 A P s t)). Qed.
Lemma lem4890332 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4890333 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term113 A P s).
Proof. exact (MK_COMB (@lem4890332 A) (@lem4890331 A P s)). Qed.
Lemma lem4890334 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term102 A P s) = (term103 A P s)) = ((term98 A P s) = (term113 A P s)).
Proof. exact (MK_COMB (@lem4890327 A P s) (@lem4890333 A P s)). Qed.
Lemma lem4890335 {A : Type'} (P : type686 A) (s : A -> Prop) : (term98 A P s) = (term113 A P s).
Proof. exact (EQ_MP (@lem4890334 A P s) (@lem4890319 A P s)). Qed.
Lemma lem4890336 {A : Type'} (P : type686 A) : (term100 A P) = (term114 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890335 A P s)). Qed.
Lemma lem4890337 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4890338 {A : Type'} (P : type686 A) : (term101 A P) = (term115 A P).
Proof. exact (MK_COMB (@lem4890337 A) (@lem4890336 A P)). Qed.
Lemma lem4890339 {A : Type'} (P : type686 A) : (term76 A P) = (term115 A P).
Proof. exact (TRANS (@lem4890315 A P) (@lem4890338 A P)). Qed.
Lemma lem4890340 {A : Type'} : (term84 A) = (term116 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4890339 A P)). Qed.
Lemma lem4890341 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4890343 {A : Type'} : (term85 A) = (term117 A).
Proof. exact (MK_COMB (@lem4890341 A) (@lem4890340 A)). Qed.
Lemma lem4890344 {A : Type'} : (term19 A) = (term117 A).
Proof. exact (TRANS (@lem4890142 A) (@lem4890343 A)). Qed.
Lemma lem4890345 {A : Type'} (h1 : term19 A) : term117 A.
Proof. exact (EQ_MP (@lem4890344 A) (@lem4890076 A h1)). Qed.
Lemma lem4890352 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term118 A P s).
Proof. exact (@lem17265 (P s) (@UNION_OF A (@FINITE (A -> Prop)) P s)). Qed.
Lemma lem4890353 {A : Type'} (P : type686 A) : (term30 A P) = (term119 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890352 A P s)). Qed.
Lemma lem4890354 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890355 {A : Type'} (P : type686 A) : (term31 A P) = (term120 A P).
Proof. exact (MK_COMB (@lem4890354 A) (@lem4890353 A P)). Qed.
Lemma lem4890356 {A : Type'} : (term32 A) = (term121 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4890355 A P)). Qed.
Lemma lem4890357 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4890414 {A : Type'} : (term20 A) = (term122 A).
Proof. exact (MK_COMB (@lem4890357 A) (@lem4890356 A)). Qed.
Lemma lem4890415 {A : Type'} (h1 : term20 A) : term122 A.
Proof. exact (EQ_MP (@lem4890414 A) (@lem4890077 A h1)). Qed.
Lemma lem4890416 {A : Type'} (P : type686 A) (h1 : term115 A P) : term115 A P.
Proof. exact (h1). Qed.
Lemma lem4890417 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term113 A P s) : term113 A P s.
Proof. exact (h1). Qed.
Lemma lem4890418 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term110 A P s t.
Proof. exact (h1). Qed.
Lemma lem4890427 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890428 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4890427 (type180 A) (type174 A) f x). Qed.
Lemma lem4890429 {A : Type'} : (@UNION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4890428 A (@UNION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4890430 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4890431 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4890429 A) (@lem4890430 A P)). Qed.
Lemma lem4890433 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890434 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4890433 (type686 A) (type686 A) f x). Qed.
Lemma lem4890435 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P) = (term123 A P).
Proof. exact (@lem4890434 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4890436 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term123 A P).
Proof. exact (TRANS (@lem4890431 A P) (@lem4890435 A P)). Qed.
Lemma lem4890437 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4890438 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term124 A P s).
Proof. exact (MK_COMB (@lem4890436 A P) (@lem4890437 A s)). Qed.
Lemma lem4890440 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890441 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4890440 (A -> Prop) Prop f x). Qed.
Lemma lem4890442 {A : Type'} (P : type686 A) (s : A -> Prop) : (term124 A P s) = (term125 A P s).
Proof. exact (@lem4890441 A (term123 A P) s). Qed.
Lemma lem4890444 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term125 A P s).
Proof. exact (TRANS (@lem4890438 A P s) (@lem4890442 A P s)). Qed.
Lemma lem4890445 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890450 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890451 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4890450 (A -> Prop) Prop f x). Qed.
Lemma lem4890453 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4890451 A P s). Qed.
Lemma lem4890454 {A : Type'} (P : type686 A) (s : A -> Prop) : (term126 A P s) = (term127 A P s).
Proof. exact (MK_COMB (@lem4890445) (@lem4890453 A P s)). Qed.
Lemma lem4890455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4890456 {A : Type'} (P : type686 A) (s : A -> Prop) : (term128 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4890455) (@lem4890454 A P s)). Qed.
Lemma lem4890457 {A : Type'} (P : type686 A) (s : A -> Prop) : (term118 A P s) = (term130 A P s).
Proof. exact (MK_COMB (@lem4890456 A P s) (@lem4890444 A P s)). Qed.
Lemma lem4890458 {A : Type'} (P : type686 A) : (term119 A P) = (term131 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890457 A P s)). Qed.
Lemma lem4890459 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890460 {A : Type'} (P : type686 A) : (term120 A P) = (term132 A P).
Proof. exact (MK_COMB (@lem4890459 A) (@lem4890458 A P)). Qed.
Lemma lem4890461 {A : Type'} : (term121 A) = (term133 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4890460 A P)). Qed.
Lemma lem4890462 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4890463 {A : Type'} : (term122 A) = (term134 A).
Proof. exact (MK_COMB (@lem4890462 A) (@lem4890461 A)). Qed.
Lemma lem4890464 {A : Type'} (h1 : term20 A) : term134 A.
Proof. exact (EQ_MP (@lem4890463 A) (@lem4890415 A h1)). Qed.
Lemma lem4890465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890475 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890476 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4890475 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4890477 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s).
Proof. exact (@lem4890476 A (@INTER A) s). Qed.
Lemma lem4890478 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4890479 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t).
Proof. exact (MK_COMB (@lem4890477 A s) (@lem4890478 A t)). Qed.
Lemma lem4890481 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890482 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4890481 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4890483 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t) = (term135 A s t).
Proof. exact (@lem4890482 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s) t). Qed.
Lemma lem4890485 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term135 A s t).
Proof. exact (TRANS (@lem4890479 A s t) (@lem4890483 A s t)). Qed.
Lemma lem4890487 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (eq_refl (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4890488 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term56 A P s t) = (term136 A P s t).
Proof. exact (MK_COMB (@lem4890487 A P) (@lem4890485 A s t)). Qed.
Lemma lem4890490 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890491 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4890490 (type180 A) (type174 A) f x). Qed.
Lemma lem4890492 {A : Type'} : (@UNION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4890491 A (@UNION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4890493 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4890494 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4890492 A) (@lem4890493 A P)). Qed.
Lemma lem4890496 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890497 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4890496 (type686 A) (type686 A) f x). Qed.
Lemma lem4890498 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P) = (term123 A P).
Proof. exact (@lem4890497 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4890499 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term123 A P).
Proof. exact (TRANS (@lem4890494 A P) (@lem4890498 A P)). Qed.
Lemma lem4890500 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term135 A s t).
Proof. exact (eq_refl (term135 A s t)). Qed.
Lemma lem4890501 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term137 A P s t).
Proof. exact (MK_COMB (@lem4890499 A P) (@lem4890500 A s t)). Qed.
Lemma lem4890503 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890504 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4890503 (A -> Prop) Prop f x). Qed.
Lemma lem4890505 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term137 A P s t) = (term138 A P s t).
Proof. exact (@lem4890504 A (term123 A P) (term135 A s t)). Qed.
Lemma lem4890506 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term138 A P s t).
Proof. exact (TRANS (@lem4890501 A P s t) (@lem4890505 A P s t)). Qed.
Lemma lem4890507 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term56 A P s t) = (term138 A P s t).
Proof. exact (TRANS (@lem4890488 A P s t) (@lem4890506 A P s t)). Qed.
Lemma lem4890508 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term139 A P s t) = (term140 A P s t).
Proof. exact (MK_COMB (@lem4890465) (@lem4890507 A P s t)). Qed.
Lemma lem4890513 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890514 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4890513 (A -> Prop) Prop f x). Qed.
Lemma lem4890516 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4890514 A P t). Qed.
Lemma lem4890521 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890522 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4890521 (A -> Prop) Prop f x). Qed.
Lemma lem4890524 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4890522 A P s). Qed.
Lemma lem4890525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4890526 {A : Type'} (P : type686 A) (s : A -> Prop) : (term141 A P s) = (term142 A P s).
Proof. exact (MK_COMB (@lem4890525) (@lem4890524 A P s)). Qed.
Lemma lem4890527 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term49 A s P t) = (term143 A s P t).
Proof. exact (MK_COMB (@lem4890526 A P s) (@lem4890516 A P t)). Qed.
Lemma lem4890528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4890529 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term144 A s P t) = (term145 A s P t).
Proof. exact (MK_COMB (@lem4890528) (@lem4890527 A s P t)). Qed.
Lemma lem4890530 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term55 A P s t) = (term146 A P s t).
Proof. exact (MK_COMB (@lem4890529 A s P t) (@lem4890508 A P s t)). Qed.
Lemma lem4890531 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4890538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890539 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4890538 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4890540 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s).
Proof. exact (@lem4890539 A (@INTER A) s). Qed.
Lemma lem4890541 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4890542 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t).
Proof. exact (MK_COMB (@lem4890540 A s) (@lem4890541 A t)). Qed.
Lemma lem4890544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890545 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4890544 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4890546 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t) = (term135 A s t).
Proof. exact (@lem4890545 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s) t). Qed.
Lemma lem4890548 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term135 A s t).
Proof. exact (TRANS (@lem4890542 A s t) (@lem4890546 A s t)). Qed.
Lemma lem4890549 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term147 A P s t).
Proof. exact (MK_COMB (@lem4890531 A P) (@lem4890548 A s t)). Qed.
Lemma lem4890551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890552 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4890551 (A -> Prop) Prop f x). Qed.
Lemma lem4890553 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term147 A P s t) = (term148 A P s t).
Proof. exact (@lem4890552 A P (term135 A s t)). Qed.
Lemma lem4890554 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term148 A P s t).
Proof. exact (TRANS (@lem4890549 A P s t) (@lem4890553 A P s t)). Qed.
Lemma lem4890555 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890560 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890561 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4890560 (A -> Prop) Prop f x). Qed.
Lemma lem4890563 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4890561 A P t). Qed.
Lemma lem4890564 {A : Type'} (P : type686 A) (t : A -> Prop) : (term126 A P t) = (term127 A P t).
Proof. exact (MK_COMB (@lem4890555) (@lem4890563 A P t)). Qed.
Lemma lem4890565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890570 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4890571 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4890570 (A -> Prop) Prop f x). Qed.
Lemma lem4890573 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4890571 A P s). Qed.
Lemma lem4890574 {A : Type'} (P : type686 A) (s : A -> Prop) : (term126 A P s) = (term127 A P s).
Proof. exact (MK_COMB (@lem4890565) (@lem4890573 A P s)). Qed.
Lemma lem4890575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4890576 {A : Type'} (P : type686 A) (s : A -> Prop) : (term128 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4890575) (@lem4890574 A P s)). Qed.
Lemma lem4890577 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term43 A s P t) = (term149 A s P t).
Proof. exact (MK_COMB (@lem4890576 A P s) (@lem4890564 A P t)). Qed.
Lemma lem4890578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4890579 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term46 A s P t) = (term150 A s P t).
Proof. exact (MK_COMB (@lem4890578) (@lem4890577 A s P t)). Qed.
Lemma lem4890580 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term48 A P s t) = (term151 A P s t).
Proof. exact (MK_COMB (@lem4890579 A s P t) (@lem4890554 A P s t)). Qed.
Lemma lem4890581 {A : Type'} (P : type686 A) (s : A -> Prop) : (term50 A P s) = (term152 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4890580 A P s t)). Qed.
Lemma lem4890582 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890583 {A : Type'} (P : type686 A) (s : A -> Prop) : (term51 A P s) = (term153 A P s).
Proof. exact (MK_COMB (@lem4890582 A) (@lem4890581 A P s)). Qed.
Lemma lem4890584 {A : Type'} (P : type686 A) : (term52 A P) = (term154 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890583 A P s)). Qed.
Lemma lem4890585 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890586 {A : Type'} (P : type686 A) : (term53 A P) = (term155 A P).
Proof. exact (MK_COMB (@lem4890585 A) (@lem4890584 A P)). Qed.
Lemma lem4890587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4890588 {A : Type'} (P : type686 A) : (term74 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem4890587) (@lem4890586 A P)). Qed.
Lemma lem4890589 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term110 A P s t) = (term157 A P s t).
Proof. exact (MK_COMB (@lem4890588 A P) (@lem4890530 A P s t)). Qed.
Lemma lem4890590 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term157 A P s t.
Proof. exact (EQ_MP (@lem4890589 A P s t) (@lem4890418 A P s t h1)). Qed.
Lemma lem4890591 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term146 A P s t.
Proof. exact (proj2 (@lem4890590 A P s t h1)). Qed.
Lemma lem4890592 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term155 A P.
Proof. exact (proj1 (@lem4890590 A P s t h1)). Qed.
Lemma lem4890594 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term143 A s P t.
Proof. exact (proj1 (@lem4890591 A P s t h1)). Qed.
Lemma lem4890604 {A : Type'} (P : type686 A) (s : A -> Prop) : (term130 A P s) = (term130 A P s).
Proof. exact (eq_refl (term130 A P s)). Qed.
Lemma lem4890605 {A : Type'} (P : type686 A) : (term131 A P) = (term131 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890604 A P s)). Qed.
Lemma lem4890606 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890607 {A : Type'} (P : type686 A) : (term132 A P) = (term132 A P).
Proof. exact (MK_COMB (@lem4890606 A) (@lem4890605 A P)). Qed.
Lemma lem4890608 {A : Type'} : (term133 A) = (term133 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4890607 A P)). Qed.
Lemma lem4890609 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4890611 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (MK_COMB (@lem4890609 A) (@lem4890608 A)). Qed.
Lemma lem4890612 {A : Type'} (h1 : term20 A) : term134 A.
Proof. exact (EQ_MP (@lem4890611 A) (@lem4890464 A h1)). Qed.
Lemma lem4890626 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term151 A P s t) = (term151 A P s t).
Proof. exact (eq_refl (term151 A P s t)). Qed.
Lemma lem4890627 {A : Type'} (P : type686 A) (s : A -> Prop) : (term152 A P s) = (term152 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4890626 A P s t)). Qed.
Lemma lem4890628 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890629 {A : Type'} (P : type686 A) (s : A -> Prop) : (term153 A P s) = (term153 A P s).
Proof. exact (MK_COMB (@lem4890628 A) (@lem4890627 A P s)). Qed.
Lemma lem4890630 {A : Type'} (P : type686 A) : (term154 A P) = (term154 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4890629 A P s)). Qed.
Lemma lem4890631 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4890633 {A : Type'} (P : type686 A) : (term155 A P) = (term155 A P).
Proof. exact (MK_COMB (@lem4890631 A) (@lem4890630 A P)). Qed.
Lemma lem4890634 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term155 A P.
Proof. exact (EQ_MP (@lem4890633 A P) (@lem4890592 A P s t h1)). Qed.
Lemma lem4890647 {A : Type'} (_60405 : type686 A) (h1 : term20 A) : term158 A _60405.
Proof. exact (@lem4890612 A h1 _60405). Qed.
Lemma lem4890648 {A : Type'} (_60405 : type686 A) : (term158 A _60405) = (term132 A _60405).
Proof. exact (eq_refl (term158 A _60405)). Qed.
Lemma lem4890649 {A : Type'} (_60405 : type686 A) (h1 : term20 A) : term132 A _60405.
Proof. exact (EQ_MP (@lem4890648 A _60405) (@lem4890647 A _60405 h1)). Qed.
Lemma lem4890650 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) (h1 : term20 A) : term159 A _60405 _60406.
Proof. exact (@lem4890649 A _60405 h1 _60406). Qed.
Lemma lem4890651 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term159 A _60405 _60406) = (term130 A _60405 _60406).
Proof. exact (eq_refl (term159 A _60405 _60406)). Qed.
Lemma lem4890653 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term160 A P _60407.
Proof. exact (@lem4890634 A P s t h1 _60407). Qed.
Lemma lem4890654 {A : Type'} (P : type686 A) (_60407 : A -> Prop) : (term160 A P _60407) = (term153 A P _60407).
Proof. exact (eq_refl (term160 A P _60407)). Qed.
Lemma lem4890655 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term153 A P _60407.
Proof. exact (EQ_MP (@lem4890654 A P _60407) (@lem4890653 A _60407 P s t h1)). Qed.
Lemma lem4890656 {A : Type'} (_60407 : A -> Prop) (_60408 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term161 A P _60407 _60408.
Proof. exact (@lem4890655 A _60407 P s t h1 _60408). Qed.
Lemma lem4890657 {A : Type'} (P : type686 A) (_60407 : A -> Prop) (_60408 : A -> Prop) : (term161 A P _60407 _60408) = (term151 A P _60407 _60408).
Proof. exact (eq_refl (term161 A P _60407 _60408)). Qed.
Lemma lem4890658 {A : Type'} (_60407 : A -> Prop) (_60408 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term151 A P _60407 _60408.
Proof. exact (EQ_MP (@lem4890657 A P _60407 _60408) (@lem4890656 A _60407 _60408 P s t h1)). Qed.
Lemma lem4890664 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) (h1 : term20 A) : term130 A _60405 _60406.
Proof. exact (EQ_MP (@lem4890651 A _60405 _60406) (@lem4890650 A _60405 _60406 h1)). Qed.
Lemma lem4890675 {A : Type'} (P : type686 A) (_60407 : A -> Prop) (_60408 : A -> Prop) : (term151 A P _60407 _60408) = (term162 A P _60407 _60408).
Proof. exact (@lem4889837 (term127 A P _60407) (term127 A P _60408) (term148 A P _60407 _60408)). Qed.
Lemma lem4890676 {A : Type'} (_60407 : A -> Prop) (_60408 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term162 A P _60407 _60408.
Proof. exact (EQ_MP (@lem4890675 A P _60407 _60408) (@lem4890658 A _60407 _60408 P s t h1)). Qed.
Lemma lem4890678 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term140 A P s t.
Proof. exact (proj2 (@lem4890591 A P s t h1)). Qed.
Lemma lem4890684 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (proj1 (@lem4890594 A P s t h1)). Qed.
Lemma lem4890685 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term163 A P s.
Proof. exact (fun h0 : term127 A P s => @lem4890684 A P s t h1). Qed.
Lemma lem4890687 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4890688 {A : Type'} (P : type686 A) (s : A -> Prop) : (term163 A P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4890687 (@I ((A -> Prop) -> Prop) P s)). Qed.
Lemma lem4890689 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (EQ_MP (@lem4890688 A P s) (@lem4890685 A P s t h1)). Qed.
Lemma lem4890691 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (proj2 (@lem4890594 A P s t h1)). Qed.
Lemma lem4890692 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term163 A P t.
Proof. exact (fun h0 : term127 A P t => @lem4890691 A P s t h1). Qed.
Lemma lem4890694 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4890695 {A : Type'} (P : type686 A) (t : A -> Prop) : (term163 A P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4890694 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4890696 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (EQ_MP (@lem4890695 A P t) (@lem4890692 A P s t h1)). Qed.
Lemma lem4890712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4890713 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term165 A P _60407 _60408) = (term166 A _60407 P _60408).
Proof. exact (@lem4890712 (term148 A P _60407 _60408) (term127 A P _60408)). Qed.
Lemma lem4890719 {A : Type'} (P : type686 A) (_60407 : A -> Prop) : (term129 A P _60407) = (term129 A P _60407).
Proof. exact (eq_refl (term129 A P _60407)). Qed.
Lemma lem4890720 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term162 A P _60407 _60408) = (term167 A _60407 P _60408).
Proof. exact (MK_COMB (@lem4890719 A P _60407) (@lem4890713 A _60407 P _60408)). Qed.
Lemma lem4890724 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4890725 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term167 A _60407 P _60408) = (term168 A _60407 P _60408).
Proof. exact (@lem4890724 (term148 A P _60407 _60408) (term127 A P _60407) (term127 A P _60408)). Qed.
Lemma lem4890741 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term162 A P _60407 _60408) = (term168 A _60407 P _60408).
Proof. exact (TRANS (@lem4890720 A _60407 P _60408) (@lem4890725 A _60407 P _60408)). Qed.
Lemma lem4890742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4890743 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term169 A P _60407 _60408) = (term170 A _60407 P _60408).
Proof. exact (MK_COMB (@lem4890742) (@lem4890741 A _60407 P _60408)). Qed.
Lemma lem4890759 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term168 A _60407 P _60408) = (term168 A _60407 P _60408).
Proof. exact (eq_refl (term168 A _60407 P _60408)). Qed.
Lemma lem4890760 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : ((term162 A P _60407 _60408) = (term168 A _60407 P _60408)) = ((term168 A _60407 P _60408) = (term168 A _60407 P _60408)).
Proof. exact (MK_COMB (@lem4890743 A _60407 P _60408) (@lem4890759 A _60407 P _60408)). Qed.
Lemma lem4890762 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4890763 (x : Prop) : (x = x) = True.
Proof. exact (@lem4890762 Prop x). Qed.
Lemma lem4890764 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : ((term168 A _60407 P _60408) = (term168 A _60407 P _60408)) = True.
Proof. exact (@lem4890763 (term168 A _60407 P _60408)). Qed.
Lemma lem4890765 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : ((term162 A P _60407 _60408) = (term168 A _60407 P _60408)) = True.
Proof. exact (TRANS (@lem4890760 A _60407 P _60408) (@lem4890764 A _60407 P _60408)). Qed.
Lemma lem4890766 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : True = ((term162 A P _60407 _60408) = (term168 A _60407 P _60408)).
Proof. exact (SYM (@lem4890765 A _60407 P _60408)). Qed.
Lemma lem4890767 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term162 A P _60407 _60408) = (term168 A _60407 P _60408).
Proof. exact (EQ_MP (@lem4890766 A _60407 P _60408) (@lem0)). Qed.
Lemma lem4890768 {A : Type'} (_60407 : A -> Prop) (_60408 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term168 A _60407 P _60408.
Proof. exact (EQ_MP (@lem4890767 A _60407 P _60408) (@lem4890676 A _60407 _60408 P s t h1)). Qed.
Lemma lem4890770 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4890771 {A : Type'} (P : type686 A) (_60407 : A -> Prop) (_60408 : A -> Prop) : (term168 A _60407 P _60408) = (term172 A P _60407 _60408).
Proof. exact (@lem4890770 (term149 A _60407 P _60408) (term148 A P _60407 _60408)). Qed.
Lemma lem4890773 (a : Prop) (b : Prop) : (term173 a b) = (term174 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4890774 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term175 A _60407 P _60408) = (term176 A _60407 P _60408).
Proof. exact (@lem4890773 (term127 A P _60407) (term127 A P _60408)). Qed.
Lemma lem4890776 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4890777 {A : Type'} (P : type686 A) (_60407 : A -> Prop) : (term178 A P _60407) = (@I ((A -> Prop) -> Prop) P _60407).
Proof. exact (@lem4890776 (@I ((A -> Prop) -> Prop) P _60407)). Qed.
Lemma lem4890778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4890779 {A : Type'} (P : type686 A) (_60407 : A -> Prop) : (term179 A P _60407) = (term142 A P _60407).
Proof. exact (MK_COMB (@lem4890778) (@lem4890777 A P _60407)). Qed.
Lemma lem4890781 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4890782 {A : Type'} (P : type686 A) (_60408 : A -> Prop) : (term178 A P _60408) = (@I ((A -> Prop) -> Prop) P _60408).
Proof. exact (@lem4890781 (@I ((A -> Prop) -> Prop) P _60408)). Qed.
Lemma lem4890783 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term176 A _60407 P _60408) = (term143 A _60407 P _60408).
Proof. exact (MK_COMB (@lem4890779 A P _60407) (@lem4890782 A P _60408)). Qed.
Lemma lem4890784 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term175 A _60407 P _60408) = (term143 A _60407 P _60408).
Proof. exact (TRANS (@lem4890774 A _60407 P _60408) (@lem4890783 A _60407 P _60408)). Qed.
Lemma lem4890785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4890786 {A : Type'} (_60407 : A -> Prop) (P : type686 A) (_60408 : A -> Prop) : (term180 A _60407 P _60408) = (term181 A _60407 P _60408).
Proof. exact (MK_COMB (@lem4890785) (@lem4890784 A _60407 P _60408)). Qed.
Lemma lem4890787 {A : Type'} (P : type686 A) (_60407 : A -> Prop) (_60408 : A -> Prop) : (term148 A P _60407 _60408) = (term148 A P _60407 _60408).
Proof. exact (eq_refl (term148 A P _60407 _60408)). Qed.
Lemma lem4890788 {A : Type'} (P : type686 A) (_60407 : A -> Prop) (_60408 : A -> Prop) : (term172 A P _60407 _60408) = (term182 A P _60407 _60408).
Proof. exact (MK_COMB (@lem4890786 A _60407 P _60408) (@lem4890787 A P _60407 _60408)). Qed.
Lemma lem4890789 {A : Type'} (P : type686 A) (_60407 : A -> Prop) (_60408 : A -> Prop) : (term168 A _60407 P _60408) = (term182 A P _60407 _60408).
Proof. exact (TRANS (@lem4890771 A P _60407 _60408) (@lem4890788 A P _60407 _60408)). Qed.
Lemma lem4890791 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term143 A s P t.
Proof. exact (conj (@lem4890689 A P s t h1) (@lem4890696 A P s t h1)). Qed.
Lemma lem4890793 {A : Type'} (_60407 : A -> Prop) (_60408 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P _60407 _60408.
Proof. exact (EQ_MP (@lem4890789 A P _60407 _60408) (@lem4890768 A _60407 _60408 P s t h1)). Qed.
Lemma lem4890794 {A : Type'} (_60407 : A -> Prop) (_60408 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P _60407 _60408.
Proof. exact (@lem4890793 A _60407 _60408 P s t h1). Qed.
Lemma lem4890795 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P s t.
Proof. exact (@lem4890794 A s t P s t h1). Qed.
Lemma lem4890798 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term148 A P s t.
Proof. exact (@lem4890795 A P s t h1 (@lem4890791 A P s t h1)). Qed.
Lemma lem4890799 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term183 A P s t.
Proof. exact (fun h0 : term184 A P s t => @lem4890798 A P s t h1). Qed.
Lemma lem4890801 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4890802 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term183 A P s t) = (term148 A P s t).
Proof. exact (@lem4890801 (term148 A P s t)). Qed.
Lemma lem4890803 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term148 A P s t.
Proof. exact (EQ_MP (@lem4890802 A P s t) (@lem4890799 A P s t h1)). Qed.
Lemma lem4890809 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4890810 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term130 A _60405 _60406) = (term185 A _60405 _60406).
Proof. exact (@lem4890809 (term125 A _60405 _60406) (term127 A _60405 _60406)). Qed.
Lemma lem4890816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4890817 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term186 A _60405 _60406) = (term187 A _60405 _60406).
Proof. exact (MK_COMB (@lem4890816) (@lem4890810 A _60405 _60406)). Qed.
Lemma lem4890823 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term185 A _60405 _60406) = (term185 A _60405 _60406).
Proof. exact (eq_refl (term185 A _60405 _60406)). Qed.
Lemma lem4890824 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : ((term130 A _60405 _60406) = (term185 A _60405 _60406)) = ((term185 A _60405 _60406) = (term185 A _60405 _60406)).
Proof. exact (MK_COMB (@lem4890817 A _60405 _60406) (@lem4890823 A _60405 _60406)). Qed.
Lemma lem4890826 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4890827 (x : Prop) : (x = x) = True.
Proof. exact (@lem4890826 Prop x). Qed.
Lemma lem4890828 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : ((term185 A _60405 _60406) = (term185 A _60405 _60406)) = True.
Proof. exact (@lem4890827 (term185 A _60405 _60406)). Qed.
Lemma lem4890829 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : ((term130 A _60405 _60406) = (term185 A _60405 _60406)) = True.
Proof. exact (TRANS (@lem4890824 A _60405 _60406) (@lem4890828 A _60405 _60406)). Qed.
Lemma lem4890830 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : True = ((term130 A _60405 _60406) = (term185 A _60405 _60406)).
Proof. exact (SYM (@lem4890829 A _60405 _60406)). Qed.
Lemma lem4890831 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term130 A _60405 _60406) = (term185 A _60405 _60406).
Proof. exact (EQ_MP (@lem4890830 A _60405 _60406) (@lem0)). Qed.
Lemma lem4890832 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) (h1 : term20 A) : term185 A _60405 _60406.
Proof. exact (EQ_MP (@lem4890831 A _60405 _60406) (@lem4890664 A _60405 _60406 h1)). Qed.
Lemma lem4890834 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4890835 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term185 A _60405 _60406) = (term188 A _60405 _60406).
Proof. exact (@lem4890834 (term127 A _60405 _60406) (term125 A _60405 _60406)). Qed.
Lemma lem4890837 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4890838 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term178 A _60405 _60406) = (@I ((A -> Prop) -> Prop) _60405 _60406).
Proof. exact (@lem4890837 (@I ((A -> Prop) -> Prop) _60405 _60406)). Qed.
Lemma lem4890839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4890840 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term189 A _60405 _60406) = (term190 A _60405 _60406).
Proof. exact (MK_COMB (@lem4890839) (@lem4890838 A _60405 _60406)). Qed.
Lemma lem4890841 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term125 A _60405 _60406) = (term125 A _60405 _60406).
Proof. exact (eq_refl (term125 A _60405 _60406)). Qed.
Lemma lem4890842 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term188 A _60405 _60406) = (term191 A _60405 _60406).
Proof. exact (MK_COMB (@lem4890840 A _60405 _60406) (@lem4890841 A _60405 _60406)). Qed.
Lemma lem4890843 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) : (term185 A _60405 _60406) = (term191 A _60405 _60406).
Proof. exact (TRANS (@lem4890835 A _60405 _60406) (@lem4890842 A _60405 _60406)). Qed.
Lemma lem4890846 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) (h1 : term20 A) : term191 A _60405 _60406.
Proof. exact (EQ_MP (@lem4890843 A _60405 _60406) (@lem4890832 A _60405 _60406 h1)). Qed.
Lemma lem4890847 {A : Type'} (_60405 : type686 A) (_60406 : A -> Prop) (h1 : term20 A) : term191 A _60405 _60406.
Proof. exact (@lem4890846 A _60405 _60406 h1). Qed.
Lemma lem4890848 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) : term192 A P s t.
Proof. exact (@lem4890847 A P (term135 A s t) h1). Qed.
Lemma lem4890851 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term138 A P s t.
Proof. exact (@lem4890848 A P s t h1 (@lem4890803 A P s t h2)). Qed.
Lemma lem4890852 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term193 A P s t.
Proof. exact (fun h0 : term140 A P s t => @lem4890851 A P s t h1 h2). Qed.
Lemma lem4890854 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4890855 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term193 A P s t) = (term138 A P s t).
Proof. exact (@lem4890854 (term138 A P s t)). Qed.
Lemma lem4890856 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term138 A P s t.
Proof. exact (EQ_MP (@lem4890855 A P s t) (@lem4890852 A P s t h1 h2)). Qed.
Lemma lem4890859 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4890861 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term140 A P s t) = (term194 A P s t).
Proof. exact (@lem4890859 (term138 A P s t)). Qed.
Lemma lem4890864 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term194 A P s t.
Proof. exact (EQ_MP (@lem4890861 A P s t) (@lem4890678 A P s t h1)). Qed.
Lemma lem4890867 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : False.
Proof. exact (@lem4890864 A P s t h2 (@lem4890856 A P s t h1 h2)). Qed.
Lemma lem4890868 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term195.
Proof. exact (fun h0 : ~ False => @lem4890867 A P s t h1 h2). Qed.
Lemma lem4890870 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4890871 : term195 = False.
Proof. exact (@lem4890870 False). Qed.
Lemma lem4890872 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : False.
Proof. exact (EQ_MP (@lem4890871) (@lem4890868 A P s t h1 h2)). Qed.
Lemma lem4890873 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term20 A) (h2 : term113 A P s) : False.
Proof. exact (ex_elim (@lem4890417 A P s h2) (fun t : A -> Prop => fun h0 : term112 A P s t => @lem4890872 A P s t h1 h0)). Qed.
Lemma lem4890874 {A : Type'} (P : type686 A) (h1 : term20 A) (h2 : term115 A P) : False.
Proof. exact (ex_elim (@lem4890416 A P h2) (fun s : A -> Prop => fun h0 : term114 A P s => @lem4890873 A P s h1 h0)). Qed.
Lemma lem4890875 {A : Type'} (h1 : term20 A) (h2 : term19 A) : False.
Proof. exact (ex_elim (@lem4890345 A h2) (fun P : type686 A => fun h0 : term116 A P => @lem4890874 A P h1 h0)). Qed.
Lemma lem4890876 {A : Type'} (h1 : term19 A) : term25 A.
Proof. exact (fun h0 : term20 A => @lem4890875 A h0 h1). Qed.
Lemma lem4890877 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem69 (term20 A)). Qed.
Lemma lem4890878 {A : Type'} (h1 : term19 A) : term26 A.
Proof. exact (EQ_MP (@lem4890877 A) (@lem4890876 A h1)). Qed.
Lemma lem4890879 {A : Type'} : term28 A.
Proof. exact (fun h0 : term19 A => @lem4890878 A h0). Qed.
Lemma lem4890880 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem4890075 A) (@lem4890879 A)). Qed.
Lemma lem4890882 {A : Type'} : term21 A.
Proof. exact (@lem4889908 A (@lem4890880 A)). Qed.
Lemma lem4890883 {A : Type'} (h1 : term19 A) : term25 A.
Proof. exact (@lem4890882 A (@lem4889890 A h1)). Qed.
Lemma lem4890884 {A : Type'} (h1 : term19 A) : False.
Proof. exact (@lem4890883 A h1 (@lem4889891 A)). Qed.
Lemma lem4890885 {A : Type'} (h1 : term19 A) : (term19 A) = False.
Proof. exact (prop_ext (fun h2 : term19 A => @lem4890884 A h1) (fun h2 : False => @lem4889890 A h1)). Qed.
Lemma lem4890886 {A : Type'} (h1 : term19 A) : False.
Proof. exact (EQ_MP (@lem4890885 A h1) (@lem4889890 A h1)). Qed.
Lemma lem4890887 {A : Type'} : term18 A.
Proof. exact (fun h0 : term19 A => @lem4890886 A h0). Qed.
Lemma lem4890888 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem4889889 A) (@lem4890887 A)). Qed.
Lemma lem4890889 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem4889885 A) (@lem4890888 A)). Qed.
