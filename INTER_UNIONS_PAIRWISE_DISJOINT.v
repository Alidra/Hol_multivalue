Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_UNIONS_PAIRWISE_DISJOINT_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXTENSION_spec.
Require Import INTER_UNIONS_spec.
Require Import IN_INTER_spec.
Require Import IN_UNION_spec.
Require Import IN_UNIONS_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_AND_EXISTS_THM_spec.
Require Import SIMPLE_IMAGE_spec.
Require Import UNIONS_IMAGE_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4829793 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4829794 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4829795 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4829794 t1) (@lem4829793 t1)). Qed.
Lemma lem4829796 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4829795 t1 t2). Qed.
Lemma lem4829797 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4829798 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4829797 t1 t2) (@lem4829796 t1 t2)). Qed.
Lemma lem4829799 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4829798 t1 t2 t3). Qed.
Lemma lem4829800 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4829801 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4829800 t1 t2 t3) (@lem4829799 t1 t2 t3)). Qed.
Lemma lem4829802 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4829801 t1 t2 t3)). Qed.
Lemma lem4829803 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term7 A u v.
Proof. exact (@lem9784 (u = v)). Qed.
Lemma lem4829804 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term7 A u v) = (term8 A u v).
Proof. exact (eq_refl (term7 A u v)). Qed.
Lemma lem4829805 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term8 A u v.
Proof. exact (EQ_MP (@lem4829804 A u v) (@lem4829803 A u v)). Qed.
Lemma lem4829806 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : u = v.
Proof. exact (h1). Qed.
Lemma lem4829807 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term9 A u v) : term9 A u v.
Proof. exact (h1). Qed.
Lemma lem4829818 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem4829819 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem4829820 {A : Type'} (P : A -> Prop) : term11 A P.
Proof. exact (EQ_MP (@lem4829819 A P) (@lem4829818 A P)). Qed.
Lemma lem4829821 {A : Type'} (P : A -> Prop) (Q : Prop) : term12 A P Q.
Proof. exact (@lem4829820 A P Q). Qed.
Lemma lem4829822 {A : Type'} (P : A -> Prop) (Q : Prop) : (term12 A P Q) = ((term13 A P Q) = (term14 A P Q)).
Proof. exact (eq_refl (term12 A P Q)). Qed.
Lemma lem4829824 {A : Type'} (P : Prop) : term15 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem4829825 {A : Type'} (P : Prop) : (term15 A P) = (term16 A P).
Proof. exact (eq_refl (term15 A P)). Qed.
Lemma lem4829826 {A : Type'} (P : Prop) : term16 A P.
Proof. exact (EQ_MP (@lem4829825 A P) (@lem4829824 A P)). Qed.
Lemma lem4829827 {A : Type'} (P : Prop) (Q : A -> Prop) : term17 A P Q.
Proof. exact (@lem4829826 A P Q). Qed.
Lemma lem4829828 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = ((term18 A P Q) = (term19 A P Q)).
Proof. exact (eq_refl (term17 A P Q)). Qed.
Lemma lem4829830 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem4829831 {A : Type'} (s : A -> Prop) : (term20 A s) = (term21 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem4829832 {A : Type'} (s : A -> Prop) : term21 A s.
Proof. exact (EQ_MP (@lem4829831 A s) (@lem4829830 A s)). Qed.
Lemma lem4829833 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term22 A s t.
Proof. exact (@lem4829832 A s t). Qed.
Lemma lem4829834 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term23 A s t).
Proof. exact (eq_refl (term22 A s t)). Qed.
Lemma lem4829835 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term23 A s t.
Proof. exact (EQ_MP (@lem4829834 A s t) (@lem4829833 A s t)). Qed.
Lemma lem4829836 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term24 A s t x.
Proof. exact (@lem4829835 A s t x). Qed.
Lemma lem4829837 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term24 A s t x) = ((term25 A x s t) = (term26 A s x t)).
Proof. exact (eq_refl (term24 A s t x)). Qed.
Lemma lem4829863 {_83095 : Type'} : term27 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4829864 {_83095 : Type'} (p : _83095 -> Prop) : term28 _83095 p.
Proof. exact (@lem4829863 _83095 p). Qed.
Lemma lem4829865 {_83095 : Type'} (p : _83095 -> Prop) : (term28 _83095 p) = (term29 _83095 p).
Proof. exact (eq_refl (term28 _83095 p)). Qed.
Lemma lem4829866 {_83095 : Type'} (p : _83095 -> Prop) : term29 _83095 p.
Proof. exact (EQ_MP (@lem4829865 _83095 p) (@lem4829864 _83095 p)). Qed.
Lemma lem4829867 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term30 _83095 p x.
Proof. exact (@lem4829866 _83095 p x). Qed.
Lemma lem4829868 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term30 _83095 p x) = ((term31 _83095 x p) = (p x)).
Proof. exact (eq_refl (term30 _83095 p x)). Qed.
Lemma lem4829877 {A : Type'} (s : A -> Prop) : term32 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem4829878 {A : Type'} (s : A -> Prop) : (term32 A s) = (term33 A s).
Proof. exact (eq_refl (term32 A s)). Qed.
Lemma lem4829879 {A : Type'} (s : A -> Prop) : term33 A s.
Proof. exact (EQ_MP (@lem4829878 A s) (@lem4829877 A s)). Qed.
Lemma lem4829880 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term34 A s t.
Proof. exact (@lem4829879 A s t). Qed.
Lemma lem4829881 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term35 A s t).
Proof. exact (eq_refl (term34 A s t)). Qed.
Lemma lem4829882 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term35 A s t.
Proof. exact (EQ_MP (@lem4829881 A s t) (@lem4829880 A s t)). Qed.
Lemma lem4829883 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term36 A s t x.
Proof. exact (@lem4829882 A s t x). Qed.
Lemma lem4829884 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term36 A s t x) = ((term37 A x s t) = (term38 A s x t)).
Proof. exact (eq_refl (term36 A s t x)). Qed.
Lemma lem4829886 {A : Type'} (s : type686 A) : term39 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem4829887 {A : Type'} (s : type686 A) : (term39 A s) = (term40 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem4829888 {A : Type'} (s : type686 A) : term40 A s.
Proof. exact (EQ_MP (@lem4829887 A s) (@lem4829886 A s)). Qed.
Lemma lem4829889 {A : Type'} (s : type686 A) (x : A) : term41 A s x.
Proof. exact (@lem4829888 A s x). Qed.
Lemma lem4829890 {A : Type'} (s : type686 A) (x : A) : (term41 A s x) = ((term42 A x s) = (term43 A s x)).
Proof. exact (eq_refl (term41 A s x)). Qed.
Lemma lem4829892 {_110510 : Type'} (s : _110510 -> Prop) : term44 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4829893 {_110510 : Type'} (s : _110510 -> Prop) : (term44 _110510 s) = (term45 _110510 s).
Proof. exact (eq_refl (term44 _110510 s)). Qed.
Lemma lem4829894 {_110510 : Type'} (s : _110510 -> Prop) : term45 _110510 s.
Proof. exact (EQ_MP (@lem4829893 _110510 s) (@lem4829892 _110510 s)). Qed.
Lemma lem4829895 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term46 _110510 s r.
Proof. exact (@lem4829894 _110510 s r). Qed.
Lemma lem4829896 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term46 _110510 s r) = ((@pairwise _110510 r s) = (term47 _110510 s r)).
Proof. exact (eq_refl (term46 _110510 s r)). Qed.
Lemma lem4829898 {A : Type'} (s : A -> Prop) : term48 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4829899 {A : Type'} (s : A -> Prop) : (term48 A s) = (term49 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem4829900 {A : Type'} (s : A -> Prop) : term49 A s.
Proof. exact (EQ_MP (@lem4829899 A s) (@lem4829898 A s)). Qed.
Lemma lem4829901 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term50 A s t.
Proof. exact (@lem4829900 A s t). Qed.
Lemma lem4829902 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = ((s = t) = (term51 A s t)).
Proof. exact (eq_refl (term50 A s t)). Qed.
Lemma lem4829904 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term52 _89422 _89438 f.
Proof. exact (@lem3452302 _89422 _89438 f). Qed.
Lemma lem4829905 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term52 _89422 _89438 f) = (term53 _89422 _89438 f).
Proof. exact (eq_refl (term52 _89422 _89438 f)). Qed.
Lemma lem4829906 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term53 _89422 _89438 f.
Proof. exact (EQ_MP (@lem4829905 _89422 _89438 f) (@lem4829904 _89422 _89438 f)). Qed.
Lemma lem4829907 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) : term54 _89422 _89438 f s.
Proof. exact (@lem4829906 _89422 _89438 f s). Qed.
Lemma lem4829908 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term54 _89422 _89438 f s) = ((term55 _89422 _89438 f s) = (term56 _89422 _89438 s f)).
Proof. exact (eq_refl (term54 _89422 _89438 f s)). Qed.
Lemma lem4829910 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term57 _88128 _88132 f.
Proof. exact (@lem3393993 _88128 _88132 f). Qed.
Lemma lem4829911 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term57 _88128 _88132 f) = (term58 _88128 _88132 f).
Proof. exact (eq_refl (term57 _88128 _88132 f)). Qed.
Lemma lem4829912 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term58 _88128 _88132 f.
Proof. exact (EQ_MP (@lem4829911 _88128 _88132 f) (@lem4829910 _88128 _88132 f)). Qed.
Lemma lem4829913 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term59 _88128 _88132 f s.
Proof. exact (@lem4829912 _88128 _88132 f s). Qed.
Lemma lem4829914 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term59 _88128 _88132 f s) = ((term60 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)).
Proof. exact (eq_refl (term59 _88128 _88132 f s)). Qed.
Lemma lem4829916 {_87026 : Type'} : term61 _87026.
Proof. exact (proj2 (@lem3341279 Prop _87026)). Qed.
Lemma lem4829917 {_87026 : Type'} (s : type686 _87026) : term62 _87026 s.
Proof. exact (@lem4829916 _87026 s). Qed.
Lemma lem4829918 {_87026 : Type'} (s : type686 _87026) : (term62 _87026 s) = (term63 _87026 s).
Proof. exact (eq_refl (term62 _87026 s)). Qed.
Lemma lem4829919 {_87026 : Type'} (s : type686 _87026) : term63 _87026 s.
Proof. exact (EQ_MP (@lem4829918 _87026 s) (@lem4829917 _87026 s)). Qed.
Lemma lem4829920 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : term64 _87026 s t.
Proof. exact (@lem4829919 _87026 s t). Qed.
Lemma lem4829921 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term64 _87026 s t) = ((term65 _87026 t s) = (term66 _87026 s t)).
Proof. exact (eq_refl (term64 _87026 s t)). Qed.
Lemma lem4829923 {_86990 : Type'} : term67 _86990.
Proof. exact (proj1 (@lem3341279 _86990 Prop)). Qed.
Lemma lem4829924 {_86990 : Type'} (s : type686 _86990) : term68 _86990 s.
Proof. exact (@lem4829923 _86990 s). Qed.
Lemma lem4829925 {_86990 : Type'} (s : type686 _86990) : (term68 _86990 s) = (term69 _86990 s).
Proof. exact (eq_refl (term68 _86990 s)). Qed.
Lemma lem4829926 {_86990 : Type'} (s : type686 _86990) : term69 _86990 s.
Proof. exact (EQ_MP (@lem4829925 _86990 s) (@lem4829924 _86990 s)). Qed.
Lemma lem4829927 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : term70 _86990 s t.
Proof. exact (@lem4829926 _86990 s t). Qed.
Lemma lem4829928 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term70 _86990 s t) = ((term71 _86990 s t) = (term72 _86990 s t)).
Proof. exact (eq_refl (term70 _86990 s t)). Qed.
Lemma lem4829935 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term71 _86990 s t) = (term72 _86990 s t).
Proof. exact (EQ_MP (@lem4829928 _86990 s t) (@lem4829927 _86990 s t)). Qed.
Lemma lem4829936 {A : Type'} (s : type686 A) (t : A -> Prop) : (term71 A s t) = (term72 A s t).
Proof. exact (@lem4829935 A s t). Qed.
Lemma lem4829937 {A : Type'} (s : type686 A) (t : type686 A) : (term73 A s t) = (term74 A s t).
Proof. exact (@lem4829936 A s (@UNIONS A t)). Qed.
Lemma lem4829939 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term60 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4829914 _88128 _88132 f s) (@lem4829913 _88128 _88132 f s)). Qed.
Lemma lem4829940 {A : Type'} (f : type672 A) (s : type686 A) : (term75 A s f) = (@IMAGE (A -> Prop) (A -> Prop) f s).
Proof. exact (@lem4829939 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4829941 {A : Type'} (t : type686 A) (s : type686 A) : (term76 A s t) = (term77 A t s).
Proof. exact (@lem4829940 A (term78 A t) s). Qed.
Lemma lem4829942 {A : Type'} (x : A -> Prop) (t : type686 A) : (term79 A t x) = (term65 A x t).
Proof. exact (eq_refl (term79 A t x)). Qed.
Lemma lem4829943 {A : Type'} (GEN_PVAR_21 : A -> Prop) (x : A -> Prop) (s : type686 A) : (term80 A GEN_PVAR_21 x s) = (term80 A GEN_PVAR_21 x s).
Proof. exact (eq_refl (term80 A GEN_PVAR_21 x s)). Qed.
Lemma lem4829944 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (x : A -> Prop) (t : type686 A) : (term81 A GEN_PVAR_21 s t x) = (term82 A GEN_PVAR_21 s x t).
Proof. exact (MK_COMB (@lem4829943 A GEN_PVAR_21 x s) (@lem4829942 A x t)). Qed.
Lemma lem4829945 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (t : type686 A) : (term83 A GEN_PVAR_21 s t) = (term84 A GEN_PVAR_21 s t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4829944 A GEN_PVAR_21 s x t)). Qed.
Lemma lem4829946 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4829947 {A : Type'} (GEN_PVAR_21 : A -> Prop) (s : type686 A) (t : type686 A) : (term85 A GEN_PVAR_21 s t) = (term86 A GEN_PVAR_21 s t).
Proof. exact (MK_COMB (@lem4829946 A) (@lem4829945 A GEN_PVAR_21 s t)). Qed.
Lemma lem4829948 {A : Type'} (s : type686 A) (t : type686 A) : (term87 A s t) = (term88 A s t).
Proof. exact (fun_ext (fun GEN_PVAR_21 : A -> Prop => @lem4829947 A GEN_PVAR_21 s t)). Qed.
Lemma lem4829949 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4829950 {A : Type'} (s : type686 A) (t : type686 A) : (term76 A s t) = (term89 A s t).
Proof. exact (MK_COMB (@lem4829949 A) (@lem4829948 A s t)). Qed.
Lemma lem4829951 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4829952 {A : Type'} (s : type686 A) (t : type686 A) : (term90 A s t) = (term91 A s t).
Proof. exact (MK_COMB (@lem4829951 A) (@lem4829950 A s t)). Qed.
Lemma lem4829953 {A : Type'} (t : type686 A) (s : type686 A) : (term77 A t s) = (term77 A t s).
Proof. exact (eq_refl (term77 A t s)). Qed.
Lemma lem4829954 {A : Type'} (t : type686 A) (s : type686 A) : ((term76 A s t) = (term77 A t s)) = ((term89 A s t) = (term77 A t s)).
Proof. exact (MK_COMB (@lem4829952 A s t) (@lem4829953 A t s)). Qed.
Lemma lem4829955 {A : Type'} (t : type686 A) (s : type686 A) : (term89 A s t) = (term77 A t s).
Proof. exact (EQ_MP (@lem4829954 A t s) (@lem4829941 A t s)). Qed.
Lemma lem4829957 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term65 _87026 t s) = (term66 _87026 s t).
Proof. exact (EQ_MP (@lem4829921 _87026 s t) (@lem4829920 _87026 s t)). Qed.
Lemma lem4829958 {A : Type'} (s : type686 A) (t : A -> Prop) : (term65 A t s) = (term66 A s t).
Proof. exact (@lem4829957 A s t). Qed.
Lemma lem4829959 {A : Type'} (t : type686 A) (x : A -> Prop) : (term65 A x t) = (term66 A t x).
Proof. exact (@lem4829958 A t x). Qed.
Lemma lem4829961 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term60 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4829914 _88128 _88132 f s) (@lem4829913 _88128 _88132 f s)). Qed.
Lemma lem4829962 {A : Type'} (f : type672 A) (s : type686 A) : (term75 A s f) = (@IMAGE (A -> Prop) (A -> Prop) f s).
Proof. exact (@lem4829961 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4829963 {A : Type'} (x : A -> Prop) (t : type686 A) : (term92 A t x) = (term93 A x t).
Proof. exact (@lem4829962 A (term94 A x) t). Qed.
Lemma lem4829964 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term95 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term95 A x x')). Qed.
Lemma lem4829965 {A : Type'} (GEN_PVAR_22 : A -> Prop) (x' : A -> Prop) (t : type686 A) : (term80 A GEN_PVAR_22 x' t) = (term80 A GEN_PVAR_22 x' t).
Proof. exact (eq_refl (term80 A GEN_PVAR_22 x' t)). Qed.
Lemma lem4829966 {A : Type'} (GEN_PVAR_22 : A -> Prop) (t : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term96 A GEN_PVAR_22 t x x') = (term97 A GEN_PVAR_22 t x x').
Proof. exact (MK_COMB (@lem4829965 A GEN_PVAR_22 x' t) (@lem4829964 A x x')). Qed.
Lemma lem4829967 {A : Type'} (GEN_PVAR_22 : A -> Prop) (t : type686 A) (x : A -> Prop) : (term98 A GEN_PVAR_22 t x) = (term99 A GEN_PVAR_22 t x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4829966 A GEN_PVAR_22 t x x')). Qed.
Lemma lem4829968 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4829969 {A : Type'} (GEN_PVAR_22 : A -> Prop) (t : type686 A) (x : A -> Prop) : (term100 A GEN_PVAR_22 t x) = (term101 A GEN_PVAR_22 t x).
Proof. exact (MK_COMB (@lem4829968 A) (@lem4829967 A GEN_PVAR_22 t x)). Qed.
Lemma lem4829970 {A : Type'} (t : type686 A) (x : A -> Prop) : (term102 A t x) = (term103 A t x).
Proof. exact (fun_ext (fun GEN_PVAR_22 : A -> Prop => @lem4829969 A GEN_PVAR_22 t x)). Qed.
Lemma lem4829971 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4829972 {A : Type'} (t : type686 A) (x : A -> Prop) : (term92 A t x) = (term104 A t x).
Proof. exact (MK_COMB (@lem4829971 A) (@lem4829970 A t x)). Qed.
Lemma lem4829973 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4829974 {A : Type'} (t : type686 A) (x : A -> Prop) : (term105 A t x) = (term106 A t x).
Proof. exact (MK_COMB (@lem4829973 A) (@lem4829972 A t x)). Qed.
Lemma lem4829975 {A : Type'} (x : A -> Prop) (t : type686 A) : (term93 A x t) = (term93 A x t).
Proof. exact (eq_refl (term93 A x t)). Qed.
Lemma lem4829976 {A : Type'} (x : A -> Prop) (t : type686 A) : ((term92 A t x) = (term93 A x t)) = ((term104 A t x) = (term93 A x t)).
Proof. exact (MK_COMB (@lem4829974 A t x) (@lem4829975 A x t)). Qed.
Lemma lem4829977 {A : Type'} (x : A -> Prop) (t : type686 A) : (term104 A t x) = (term93 A x t).
Proof. exact (EQ_MP (@lem4829976 A x t) (@lem4829963 A x t)). Qed.
Lemma lem4829978 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4829979 {A : Type'} (x : A -> Prop) (t : type686 A) : (term66 A t x) = (term107 A x t).
Proof. exact (MK_COMB (@lem4829978 A) (@lem4829977 A x t)). Qed.
Lemma lem4829981 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term55 _89422 _89438 f s) = (term56 _89422 _89438 s f).
Proof. exact (EQ_MP (@lem4829908 _89422 _89438 s f) (@lem4829907 _89422 _89438 f s)). Qed.
Lemma lem4829982 {A : Type'} (s : type686 A) (f : type672 A) : (term108 A f s) = (term109 A s f).
Proof. exact (@lem4829981 A (A -> Prop) s f). Qed.
Lemma lem4829983 {A : Type'} (t : type686 A) (x : A -> Prop) : (term107 A x t) = (term110 A t x).
Proof. exact (@lem4829982 A t (term94 A x)). Qed.
Lemma lem4829995 {A B : Type'} (f : A -> B) (y : A) : (term111 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4829996 {A : Type'} (f : type672 A) (y : A -> Prop) : (term112 A f y) = (f y).
Proof. exact (@lem4829995 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4829997 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term113 A x x') = (term95 A x x').
Proof. exact (@lem4829996 A (term94 A x) x'). Qed.
Lemma lem4829998 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term95 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term95 A x x')). Qed.
Lemma lem4829999 {A : Type'} (x : A -> Prop) : (term114 A x) = (term94 A x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4829998 A x x')). Qed.
Lemma lem4830000 {A : Type'} (x' : A -> Prop) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4830001 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term113 A x x') = (term95 A x x').
Proof. exact (MK_COMB (@lem4829999 A x) (@lem4830000 A x')). Qed.
Lemma lem4830002 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4830003 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term115 A x x') = (term116 A x x').
Proof. exact (MK_COMB (@lem4830002 A) (@lem4830001 A x x')). Qed.
Lemma lem4830004 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term95 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term95 A x x')). Qed.
Lemma lem4830005 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : ((term113 A x x') = (term95 A x x')) = ((term95 A x x') = (@INTER A x x')).
Proof. exact (MK_COMB (@lem4830003 A x x') (@lem4830004 A x x')). Qed.
Lemma lem4830006 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term95 A x x') = (@INTER A x x').
Proof. exact (EQ_MP (@lem4830005 A x x') (@lem4829997 A x x')). Qed.
Lemma lem4830007 {A : Type'} (y : A) : (@IN A y) = (@IN A y).
Proof. exact (eq_refl (@IN A y)). Qed.
Lemma lem4830008 {A : Type'} (y : A) (x : A -> Prop) (x' : A -> Prop) : (term117 A y x x') = (term37 A y x x').
Proof. exact (MK_COMB (@lem4830007 A y) (@lem4830006 A x x')). Qed.
Lemma lem4830009 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term118 A x' t) = (term118 A x' t).
Proof. exact (eq_refl (term118 A x' t)). Qed.
Lemma lem4830010 {A : Type'} (t : type686 A) (y : A) (x : A -> Prop) (x' : A -> Prop) : (term119 A t y x x') = (term120 A t y x x').
Proof. exact (MK_COMB (@lem4830009 A x' t) (@lem4830008 A y x x')). Qed.
Lemma lem4830013 {A : Type'} (t : type686 A) (y : A) (x : A -> Prop) : (term121 A t y x) = (term122 A t y x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830010 A t y x x')). Qed.
Lemma lem4830014 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830015 {A : Type'} (t : type686 A) (y : A) (x : A -> Prop) : (term123 A t y x) = (term124 A t y x).
Proof. exact (MK_COMB (@lem4830014 A) (@lem4830013 A t y x)). Qed.
Lemma lem4830020 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem4830021 {A : Type'} (GEN_PVAR_47 : A) (t : type686 A) (y : A) (x : A -> Prop) : (term125 A GEN_PVAR_47 t y x) = (term126 A GEN_PVAR_47 t y x).
Proof. exact (MK_COMB (@lem4830020 A GEN_PVAR_47) (@lem4830015 A t y x)). Qed.
Lemma lem4830022 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4830023 {A : Type'} (GEN_PVAR_47 : A) (t : type686 A) (x : A -> Prop) (y : A) : (term127 A GEN_PVAR_47 t x y) = (term128 A GEN_PVAR_47 t x y).
Proof. exact (MK_COMB (@lem4830021 A GEN_PVAR_47 t y x) (@lem4830022 A y)). Qed.
Lemma lem4830024 {A : Type'} (GEN_PVAR_47 : A) (t : type686 A) (x : A -> Prop) : (term129 A GEN_PVAR_47 t x) = (term130 A GEN_PVAR_47 t x).
Proof. exact (fun_ext (fun y : A => @lem4830023 A GEN_PVAR_47 t x y)). Qed.
Lemma lem4830025 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4830026 {A : Type'} (GEN_PVAR_47 : A) (t : type686 A) (x : A -> Prop) : (term131 A GEN_PVAR_47 t x) = (term132 A GEN_PVAR_47 t x).
Proof. exact (MK_COMB (@lem4830025 A) (@lem4830024 A GEN_PVAR_47 t x)). Qed.
Lemma lem4830031 {A : Type'} (t : type686 A) (x : A -> Prop) : (term133 A t x) = (term134 A t x).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem4830026 A GEN_PVAR_47 t x)). Qed.
Lemma lem4830032 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4830033 {A : Type'} (t : type686 A) (x : A -> Prop) : (term110 A t x) = (term135 A t x).
Proof. exact (MK_COMB (@lem4830032 A) (@lem4830031 A t x)). Qed.
Lemma lem4830034 {A : Type'} (t : type686 A) (x : A -> Prop) : (term107 A x t) = (term135 A t x).
Proof. exact (TRANS (@lem4829983 A t x) (@lem4830033 A t x)). Qed.
Lemma lem4830035 {A : Type'} (t : type686 A) (x : A -> Prop) : (term66 A t x) = (term135 A t x).
Proof. exact (TRANS (@lem4829979 A x t) (@lem4830034 A t x)). Qed.
Lemma lem4830036 {A : Type'} (t : type686 A) (x : A -> Prop) : (term65 A x t) = (term135 A t x).
Proof. exact (TRANS (@lem4829959 A t x) (@lem4830035 A t x)). Qed.
Lemma lem4830037 {A : Type'} (t : type686 A) : (term78 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830036 A t x)). Qed.
Lemma lem4830038 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4830039 {A : Type'} (t : type686 A) : (term137 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem4830038 A) (@lem4830037 A t)). Qed.
Lemma lem4830040 {A : Type'} (s : type686 A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4830041 {A : Type'} (t : type686 A) (s : type686 A) : (term77 A t s) = (term139 A t s).
Proof. exact (MK_COMB (@lem4830039 A t) (@lem4830040 A s)). Qed.
Lemma lem4830042 {A : Type'} (t : type686 A) (s : type686 A) : (term89 A s t) = (term139 A t s).
Proof. exact (TRANS (@lem4829955 A t s) (@lem4830041 A t s)). Qed.
Lemma lem4830043 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4830044 {A : Type'} (t : type686 A) (s : type686 A) : (term74 A s t) = (term140 A t s).
Proof. exact (MK_COMB (@lem4830043 A) (@lem4830042 A t s)). Qed.
Lemma lem4830046 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term55 _89422 _89438 f s) = (term56 _89422 _89438 s f).
Proof. exact (EQ_MP (@lem4829908 _89422 _89438 s f) (@lem4829907 _89422 _89438 f s)). Qed.
Lemma lem4830047 {A : Type'} (s : type686 A) (f : type672 A) : (term108 A f s) = (term109 A s f).
Proof. exact (@lem4830046 A (A -> Prop) s f). Qed.
Lemma lem4830048 {A : Type'} (s : type686 A) (t : type686 A) : (term140 A t s) = (term141 A s t).
Proof. exact (@lem4830047 A s (term136 A t)). Qed.
Lemma lem4830060 {A B : Type'} (f : A -> B) (y : A) : (term111 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4830061 {A : Type'} (f : type672 A) (y : A -> Prop) : (term112 A f y) = (f y).
Proof. exact (@lem4830060 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4830062 {A : Type'} (t : type686 A) (x : A -> Prop) : (term142 A t x) = (term143 A t x).
Proof. exact (@lem4830061 A (term136 A t) x). Qed.
Lemma lem4830063 {A : Type'} (t : type686 A) (x : A -> Prop) : (term143 A t x) = (term135 A t x).
Proof. exact (eq_refl (term143 A t x)). Qed.
Lemma lem4830064 {A : Type'} (t : type686 A) : (term144 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830063 A t x)). Qed.
Lemma lem4830065 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4830066 {A : Type'} (t : type686 A) (x : A -> Prop) : (term142 A t x) = (term143 A t x).
Proof. exact (MK_COMB (@lem4830064 A t) (@lem4830065 A x)). Qed.
Lemma lem4830067 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4830068 {A : Type'} (t : type686 A) (x : A -> Prop) : (term145 A t x) = (term146 A t x).
Proof. exact (MK_COMB (@lem4830067 A) (@lem4830066 A t x)). Qed.
Lemma lem4830069 {A : Type'} (t : type686 A) (x : A -> Prop) : (term143 A t x) = (term135 A t x).
Proof. exact (eq_refl (term143 A t x)). Qed.
Lemma lem4830070 {A : Type'} (t : type686 A) (x : A -> Prop) : ((term142 A t x) = (term143 A t x)) = ((term143 A t x) = (term135 A t x)).
Proof. exact (MK_COMB (@lem4830068 A t x) (@lem4830069 A t x)). Qed.
Lemma lem4830071 {A : Type'} (t : type686 A) (x : A -> Prop) : (term143 A t x) = (term135 A t x).
Proof. exact (EQ_MP (@lem4830070 A t x) (@lem4830062 A t x)). Qed.
Lemma lem4830082 {A : Type'} (y : A) : (@IN A y) = (@IN A y).
Proof. exact (eq_refl (@IN A y)). Qed.
Lemma lem4830083 {A : Type'} (y : A) (t : type686 A) (x : A -> Prop) : (term147 A y t x) = (term148 A y t x).
Proof. exact (MK_COMB (@lem4830082 A y) (@lem4830071 A t x)). Qed.
Lemma lem4830084 {A : Type'} (x : A -> Prop) (s : type686 A) : (term118 A x s) = (term118 A x s).
Proof. exact (eq_refl (term118 A x s)). Qed.
Lemma lem4830085 {A : Type'} (s : type686 A) (y : A) (t : type686 A) (x : A -> Prop) : (term149 A s y t x) = (term150 A s y t x).
Proof. exact (MK_COMB (@lem4830084 A x s) (@lem4830083 A y t x)). Qed.
Lemma lem4830088 {A : Type'} (s : type686 A) (y : A) (t : type686 A) : (term151 A s y t) = (term152 A s y t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830085 A s y t x)). Qed.
Lemma lem4830089 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830090 {A : Type'} (s : type686 A) (y : A) (t : type686 A) : (term153 A s y t) = (term154 A s y t).
Proof. exact (MK_COMB (@lem4830089 A) (@lem4830088 A s y t)). Qed.
Lemma lem4830095 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem4830096 {A : Type'} (GEN_PVAR_47 : A) (s : type686 A) (y : A) (t : type686 A) : (term155 A GEN_PVAR_47 s y t) = (term156 A GEN_PVAR_47 s y t).
Proof. exact (MK_COMB (@lem4830095 A GEN_PVAR_47) (@lem4830090 A s y t)). Qed.
Lemma lem4830097 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4830098 {A : Type'} (GEN_PVAR_47 : A) (s : type686 A) (t : type686 A) (y : A) : (term157 A GEN_PVAR_47 s t y) = (term158 A GEN_PVAR_47 s t y).
Proof. exact (MK_COMB (@lem4830096 A GEN_PVAR_47 s y t) (@lem4830097 A y)). Qed.
Lemma lem4830099 {A : Type'} (GEN_PVAR_47 : A) (s : type686 A) (t : type686 A) : (term159 A GEN_PVAR_47 s t) = (term160 A GEN_PVAR_47 s t).
Proof. exact (fun_ext (fun y : A => @lem4830098 A GEN_PVAR_47 s t y)). Qed.
Lemma lem4830100 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4830101 {A : Type'} (GEN_PVAR_47 : A) (s : type686 A) (t : type686 A) : (term161 A GEN_PVAR_47 s t) = (term162 A GEN_PVAR_47 s t).
Proof. exact (MK_COMB (@lem4830100 A) (@lem4830099 A GEN_PVAR_47 s t)). Qed.
Lemma lem4830106 {A : Type'} (s : type686 A) (t : type686 A) : (term163 A s t) = (term164 A s t).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem4830101 A GEN_PVAR_47 s t)). Qed.
Lemma lem4830107 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4830108 {A : Type'} (s : type686 A) (t : type686 A) : (term141 A s t) = (term165 A s t).
Proof. exact (MK_COMB (@lem4830107 A) (@lem4830106 A s t)). Qed.
Lemma lem4830109 {A : Type'} (s : type686 A) (t : type686 A) : (term140 A t s) = (term165 A s t).
Proof. exact (TRANS (@lem4830048 A s t) (@lem4830108 A s t)). Qed.
Lemma lem4830110 {A : Type'} (s : type686 A) (t : type686 A) : (term74 A s t) = (term165 A s t).
Proof. exact (TRANS (@lem4830044 A t s) (@lem4830109 A s t)). Qed.
Lemma lem4830111 {A : Type'} (s : type686 A) (t : type686 A) : (term73 A s t) = (term165 A s t).
Proof. exact (TRANS (@lem4829937 A s t) (@lem4830110 A s t)). Qed.
Lemma lem4830112 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4830113 {A : Type'} (s : type686 A) (t : type686 A) : (term166 A s t) = (term167 A s t).
Proof. exact (MK_COMB (@lem4830112 A) (@lem4830111 A s t)). Qed.
Lemma lem4830114 {A : Type'} (s : type686 A) (t : type686 A) : (term168 A s t) = (term168 A s t).
Proof. exact (eq_refl (term168 A s t)). Qed.
Lemma lem4830115 {A : Type'} (s : type686 A) (t : type686 A) : ((term73 A s t) = (term168 A s t)) = ((term165 A s t) = (term168 A s t)).
Proof. exact (MK_COMB (@lem4830113 A s t) (@lem4830114 A s t)). Qed.
Lemma lem4830118 {A : Type'} (s : type686 A) (t : type686 A) : (term169 A s t) = (term169 A s t).
Proof. exact (eq_refl (term169 A s t)). Qed.
Lemma lem4830119 {A : Type'} (s : type686 A) (t : type686 A) : (term170 A s t) = (term171 A s t).
Proof. exact (MK_COMB (@lem4830118 A s t) (@lem4830115 A s t)). Qed.
Lemma lem4830122 {A : Type'} (s : type686 A) (t : type686 A) : (term171 A s t) = (term170 A s t).
Proof. exact (SYM (@lem4830119 A s t)). Qed.
Lemma lem4830124 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term51 A s t).
Proof. exact (EQ_MP (@lem4829902 A s t) (@lem4829901 A s t)). Qed.
Lemma lem4830125 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term51 A s t).
Proof. exact (@lem4830124 A s t). Qed.
Lemma lem4830126 {A : Type'} (s : type686 A) (t : type686 A) : ((term165 A s t) = (term168 A s t)) = (term172 A s t).
Proof. exact (@lem4830125 A (term165 A s t) (term168 A s t)). Qed.
Lemma lem4830127 {A : Type'} (s : type686 A) (t : type686 A) : (term169 A s t) = (term169 A s t).
Proof. exact (eq_refl (term169 A s t)). Qed.
Lemma lem4830128 {A : Type'} (s : type686 A) (t : type686 A) : (term171 A s t) = (term173 A s t).
Proof. exact (MK_COMB (@lem4830127 A s t) (@lem4830126 A s t)). Qed.
Lemma lem4830129 {A : Type'} (s : type686 A) (t : type686 A) : (term173 A s t) = (term171 A s t).
Proof. exact (SYM (@lem4830128 A s t)). Qed.
Lemma lem4830133 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term47 _110510 s r).
Proof. exact (EQ_MP (@lem4829896 _110510 s r) (@lem4829895 _110510 s r)). Qed.
Lemma lem4830134 {A : Type'} (s : type686 A) (r : type639 A) : (@pairwise (A -> Prop) r s) = (term174 A s r).
Proof. exact (@lem4830133 (A -> Prop) s r). Qed.
Lemma lem4830135 {A : Type'} (s : type686 A) (t : type686 A) : (term175 A s t) = (term176 A s t).
Proof. exact (@lem4830134 A (@UNION (A -> Prop) s t) (@DISJOINT A)). Qed.
Lemma lem4830149 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem4829837 A s x t) (@lem4829836 A s t x)). Qed.
Lemma lem4830150 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term177 A x s t) = (term178 A s x t).
Proof. exact (@lem4830149 (A -> Prop) s x t). Qed.
Lemma lem4830153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4830154 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term179 A x s t) = (term180 A s x t).
Proof. exact (MK_COMB (@lem4830153) (@lem4830150 A s x t)). Qed.
Lemma lem4830158 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem4829837 A s x t) (@lem4829836 A s t x)). Qed.
Lemma lem4830159 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term177 A x s t) = (term178 A s x t).
Proof. exact (@lem4830158 (A -> Prop) s x t). Qed.
Lemma lem4830160 {A : Type'} (s : type686 A) (y : A -> Prop) (t : type686 A) : (term177 A y s t) = (term178 A s y t).
Proof. exact (@lem4830159 A s y t). Qed.
Lemma lem4830163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4830164 {A : Type'} (s : type686 A) (y : A -> Prop) (t : type686 A) : (term179 A y s t) = (term180 A s y t).
Proof. exact (MK_COMB (@lem4830163) (@lem4830160 A s y t)). Qed.
Lemma lem4830167 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term9 A x y) = (term9 A x y).
Proof. exact (eq_refl (term9 A x y)). Qed.
Lemma lem4830168 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (y : A -> Prop) : (term181 A s t x y) = (term182 A s t x y).
Proof. exact (MK_COMB (@lem4830164 A s y t) (@lem4830167 A x y)). Qed.
Lemma lem4830171 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (y : A -> Prop) : (term183 A s t x y) = (term184 A s t x y).
Proof. exact (MK_COMB (@lem4830154 A s x t) (@lem4830168 A s t x y)). Qed.
Lemma lem4830174 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4830175 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (y : A -> Prop) : (term185 A s t x y) = (term186 A s t x y).
Proof. exact (MK_COMB (@lem4830174) (@lem4830171 A s t x y)). Qed.
Lemma lem4830176 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (@DISJOINT A x y) = (@DISJOINT A x y).
Proof. exact (eq_refl (@DISJOINT A x y)). Qed.
Lemma lem4830177 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (y : A -> Prop) : (term187 A s t x y) = (term188 A s t x y).
Proof. exact (MK_COMB (@lem4830175 A s t x y) (@lem4830176 A x y)). Qed.
Lemma lem4830180 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term189 A s t x) = (term190 A s t x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4830177 A s t x y)). Qed.
Lemma lem4830181 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4830182 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) : (term191 A s t x) = (term192 A s t x).
Proof. exact (MK_COMB (@lem4830181 A) (@lem4830180 A s t x)). Qed.
Lemma lem4830187 {A : Type'} (s : type686 A) (t : type686 A) : (term193 A s t) = (term194 A s t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830182 A s t x)). Qed.
Lemma lem4830188 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4830189 {A : Type'} (s : type686 A) (t : type686 A) : (term176 A s t) = (term195 A s t).
Proof. exact (MK_COMB (@lem4830188 A) (@lem4830187 A s t)). Qed.
Lemma lem4830194 {A : Type'} (s : type686 A) (t : type686 A) : (term175 A s t) = (term195 A s t).
Proof. exact (TRANS (@lem4830135 A s t) (@lem4830189 A s t)). Qed.
Lemma lem4830195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4830196 {A : Type'} (s : type686 A) (t : type686 A) : (term169 A s t) = (term196 A s t).
Proof. exact (MK_COMB (@lem4830195) (@lem4830194 A s t)). Qed.
Lemma lem4830204 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term31 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4829868 _83095 p x) (@lem4829867 _83095 p x)). Qed.
Lemma lem4830205 {A : Type'} (p : A -> Prop) (x : A) : (term31 A x p) = (p x).
Proof. exact (@lem4830204 A p x). Qed.
Lemma lem4830206 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term197 A x s t) = (term198 A s t x).
Proof. exact (@lem4830205 A (term199 A s t) x). Qed.
Lemma lem4830207 {A : Type'} (s : type686 A) (y : A) (t : type686 A) : (term198 A s t y) = (term154 A s y t).
Proof. exact (eq_refl (term198 A s t y)). Qed.
Lemma lem4830208 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem4830209 {A : Type'} (GEN_PVAR_47 : A) (s : type686 A) (y : A) (t : type686 A) : (term200 A GEN_PVAR_47 s t y) = (term156 A GEN_PVAR_47 s y t).
Proof. exact (MK_COMB (@lem4830208 A GEN_PVAR_47) (@lem4830207 A s y t)). Qed.
Lemma lem4830210 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4830211 {A : Type'} (GEN_PVAR_47 : A) (s : type686 A) (t : type686 A) (y : A) : (term201 A GEN_PVAR_47 s t y) = (term158 A GEN_PVAR_47 s t y).
Proof. exact (MK_COMB (@lem4830209 A GEN_PVAR_47 s y t) (@lem4830210 A y)). Qed.
Lemma lem4830212 {A : Type'} (GEN_PVAR_47 : A) (s : type686 A) (t : type686 A) : (term202 A GEN_PVAR_47 s t) = (term160 A GEN_PVAR_47 s t).
Proof. exact (fun_ext (fun y : A => @lem4830211 A GEN_PVAR_47 s t y)). Qed.
Lemma lem4830213 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4830214 {A : Type'} (GEN_PVAR_47 : A) (s : type686 A) (t : type686 A) : (term203 A GEN_PVAR_47 s t) = (term162 A GEN_PVAR_47 s t).
Proof. exact (MK_COMB (@lem4830213 A) (@lem4830212 A GEN_PVAR_47 s t)). Qed.
Lemma lem4830215 {A : Type'} (s : type686 A) (t : type686 A) : (term204 A s t) = (term164 A s t).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem4830214 A GEN_PVAR_47 s t)). Qed.
Lemma lem4830216 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4830217 {A : Type'} (s : type686 A) (t : type686 A) : (term205 A s t) = (term165 A s t).
Proof. exact (MK_COMB (@lem4830216 A) (@lem4830215 A s t)). Qed.
Lemma lem4830218 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4830219 {A : Type'} (x : A) (s : type686 A) (t : type686 A) : (term197 A x s t) = (term206 A x s t).
Proof. exact (MK_COMB (@lem4830218 A x) (@lem4830217 A s t)). Qed.
Lemma lem4830220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4830221 {A : Type'} (x : A) (s : type686 A) (t : type686 A) : (term207 A x s t) = (term208 A x s t).
Proof. exact (MK_COMB (@lem4830220) (@lem4830219 A x s t)). Qed.
Lemma lem4830222 {A : Type'} (s : type686 A) (x : A) (t : type686 A) : (term198 A s t x) = (term154 A s x t).
Proof. exact (eq_refl (term198 A s t x)). Qed.
Lemma lem4830223 {A : Type'} (s : type686 A) (x : A) (t : type686 A) : ((term197 A x s t) = (term198 A s t x)) = ((term206 A x s t) = (term154 A s x t)).
Proof. exact (MK_COMB (@lem4830221 A x s t) (@lem4830222 A s x t)). Qed.
Lemma lem4830224 {A : Type'} (s : type686 A) (x : A) (t : type686 A) : (term206 A x s t) = (term154 A s x t).
Proof. exact (EQ_MP (@lem4830223 A s x t) (@lem4830206 A s t x)). Qed.
Lemma lem4830232 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term31 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4829868 _83095 p x) (@lem4829867 _83095 p x)). Qed.
Lemma lem4830233 {A : Type'} (p : A -> Prop) (x : A) : (term31 A x p) = (p x).
Proof. exact (@lem4830232 A p x). Qed.
Lemma lem4830234 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A) : (term209 A x' t x) = (term210 A t x x').
Proof. exact (@lem4830233 A (term211 A t x) x'). Qed.
Lemma lem4830235 {A : Type'} (t : type686 A) (y : A) (x : A -> Prop) : (term210 A t x y) = (term124 A t y x).
Proof. exact (eq_refl (term210 A t x y)). Qed.
Lemma lem4830236 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem4830237 {A : Type'} (GEN_PVAR_47 : A) (t : type686 A) (y : A) (x : A -> Prop) : (term212 A GEN_PVAR_47 t x y) = (term126 A GEN_PVAR_47 t y x).
Proof. exact (MK_COMB (@lem4830236 A GEN_PVAR_47) (@lem4830235 A t y x)). Qed.
Lemma lem4830238 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4830239 {A : Type'} (GEN_PVAR_47 : A) (t : type686 A) (x : A -> Prop) (y : A) : (term213 A GEN_PVAR_47 t x y) = (term128 A GEN_PVAR_47 t x y).
Proof. exact (MK_COMB (@lem4830237 A GEN_PVAR_47 t y x) (@lem4830238 A y)). Qed.
Lemma lem4830240 {A : Type'} (GEN_PVAR_47 : A) (t : type686 A) (x : A -> Prop) : (term214 A GEN_PVAR_47 t x) = (term130 A GEN_PVAR_47 t x).
Proof. exact (fun_ext (fun y : A => @lem4830239 A GEN_PVAR_47 t x y)). Qed.
Lemma lem4830241 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4830242 {A : Type'} (GEN_PVAR_47 : A) (t : type686 A) (x : A -> Prop) : (term215 A GEN_PVAR_47 t x) = (term132 A GEN_PVAR_47 t x).
Proof. exact (MK_COMB (@lem4830241 A) (@lem4830240 A GEN_PVAR_47 t x)). Qed.
Lemma lem4830243 {A : Type'} (t : type686 A) (x : A -> Prop) : (term216 A t x) = (term134 A t x).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem4830242 A GEN_PVAR_47 t x)). Qed.
Lemma lem4830244 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4830245 {A : Type'} (t : type686 A) (x : A -> Prop) : (term217 A t x) = (term135 A t x).
Proof. exact (MK_COMB (@lem4830244 A) (@lem4830243 A t x)). Qed.
Lemma lem4830246 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4830247 {A : Type'} (x : A) (t : type686 A) (x' : A -> Prop) : (term209 A x t x') = (term148 A x t x').
Proof. exact (MK_COMB (@lem4830246 A x) (@lem4830245 A t x')). Qed.
Lemma lem4830248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4830249 {A : Type'} (x : A) (t : type686 A) (x' : A -> Prop) : (term218 A x t x') = (term219 A x t x').
Proof. exact (MK_COMB (@lem4830248) (@lem4830247 A x t x')). Qed.
Lemma lem4830250 {A : Type'} (t : type686 A) (x : A) (x' : A -> Prop) : (term210 A t x' x) = (term124 A t x x').
Proof. exact (eq_refl (term210 A t x' x)). Qed.
Lemma lem4830251 {A : Type'} (t : type686 A) (x : A) (x' : A -> Prop) : ((term209 A x t x') = (term210 A t x' x)) = ((term148 A x t x') = (term124 A t x x')).
Proof. exact (MK_COMB (@lem4830249 A x t x') (@lem4830250 A t x x')). Qed.
Lemma lem4830252 {A : Type'} (t : type686 A) (x : A) (x' : A -> Prop) : (term148 A x t x') = (term124 A t x x').
Proof. exact (EQ_MP (@lem4830251 A t x x') (@lem4830234 A t x' x)). Qed.
Lemma lem4830260 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A x s t) = (term38 A s x t).
Proof. exact (EQ_MP (@lem4829884 A s x t) (@lem4829883 A s t x)). Qed.
Lemma lem4830261 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A x s t) = (term38 A s x t).
Proof. exact (@lem4830260 A s x t). Qed.
Lemma lem4830262 {A : Type'} (x : A -> Prop) (x' : A) (x'' : A -> Prop) : (term37 A x' x x'') = (term38 A x x' x'').
Proof. exact (@lem4830261 A x x' x''). Qed.
Lemma lem4830265 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term118 A x' t) = (term118 A x' t).
Proof. exact (eq_refl (term118 A x' t)). Qed.
Lemma lem4830266 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A) (x'' : A -> Prop) : (term120 A t x' x x'') = (term220 A t x x' x'').
Proof. exact (MK_COMB (@lem4830265 A x'' t) (@lem4830262 A x x' x'')). Qed.
Lemma lem4830269 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A) : (term122 A t x' x) = (term221 A t x x').
Proof. exact (fun_ext (fun x'' : A -> Prop => @lem4830266 A t x x' x'')). Qed.
Lemma lem4830270 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830271 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A) : (term124 A t x' x) = (term222 A t x x').
Proof. exact (MK_COMB (@lem4830270 A) (@lem4830269 A t x x')). Qed.
Lemma lem4830276 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A) : (term148 A x' t x) = (term222 A t x x').
Proof. exact (TRANS (@lem4830252 A t x' x) (@lem4830271 A t x x')). Qed.
Lemma lem4830277 {A : Type'} (x : A -> Prop) (s : type686 A) : (term118 A x s) = (term118 A x s).
Proof. exact (eq_refl (term118 A x s)). Qed.
Lemma lem4830278 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (x' : A) : (term150 A s x' t x) = (term223 A s t x x').
Proof. exact (MK_COMB (@lem4830277 A x s) (@lem4830276 A t x x')). Qed.
Lemma lem4830281 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term152 A s x t) = (term224 A s t x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830278 A s t x' x)). Qed.
Lemma lem4830282 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830283 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term154 A s x t) = (term225 A s t x).
Proof. exact (MK_COMB (@lem4830282 A) (@lem4830281 A s t x)). Qed.
Lemma lem4830288 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term206 A x s t) = (term225 A s t x).
Proof. exact (TRANS (@lem4830224 A s x t) (@lem4830283 A s t x)). Qed.
Lemma lem4830289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4830290 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term208 A x s t) = (term226 A s t x).
Proof. exact (MK_COMB (@lem4830289) (@lem4830288 A s t x)). Qed.
Lemma lem4830292 {A : Type'} (s : type686 A) (x : A) : (term42 A x s) = (term43 A s x).
Proof. exact (EQ_MP (@lem4829890 A s x) (@lem4829889 A s x)). Qed.
Lemma lem4830293 {A : Type'} (s : type686 A) (x : A) : (term42 A x s) = (term43 A s x).
Proof. exact (@lem4830292 A s x). Qed.
Lemma lem4830294 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term227 A x s t) = (term228 A s t x).
Proof. exact (@lem4830293 A (@INTER (A -> Prop) s t) x). Qed.
Lemma lem4830302 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A x s t) = (term38 A s x t).
Proof. exact (EQ_MP (@lem4829884 A s x t) (@lem4829883 A s t x)). Qed.
Lemma lem4830303 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term229 A x s t) = (term230 A s x t).
Proof. exact (@lem4830302 (A -> Prop) s x t). Qed.
Lemma lem4830304 {A : Type'} (s : type686 A) (t : A -> Prop) (t' : type686 A) : (term229 A t s t') = (term230 A s t t').
Proof. exact (@lem4830303 A s t t'). Qed.
Lemma lem4830307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4830308 {A : Type'} (s : type686 A) (t : A -> Prop) (t' : type686 A) : (term231 A t s t') = (term232 A s t t').
Proof. exact (MK_COMB (@lem4830307) (@lem4830304 A s t t')). Qed.
Lemma lem4830309 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@IN A x t).
Proof. exact (eq_refl (@IN A x t)). Qed.
Lemma lem4830310 {A : Type'} (s : type686 A) (t : type686 A) (x : A) (t' : A -> Prop) : (term233 A s t x t') = (term234 A s t x t').
Proof. exact (MK_COMB (@lem4830308 A s t' t) (@lem4830309 A x t')). Qed.
Lemma lem4830313 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term235 A s t x) = (term236 A s t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4830310 A s t x t')). Qed.
Lemma lem4830314 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830315 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term228 A s t x) = (term237 A s t x).
Proof. exact (MK_COMB (@lem4830314 A) (@lem4830313 A s t x)). Qed.
Lemma lem4830320 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : (term227 A x s t) = (term237 A s t x).
Proof. exact (TRANS (@lem4830294 A s t x) (@lem4830315 A s t x)). Qed.
Lemma lem4830321 {A : Type'} (s : type686 A) (t : type686 A) (x : A) : ((term206 A x s t) = (term227 A x s t)) = ((term225 A s t x) = (term237 A s t x)).
Proof. exact (MK_COMB (@lem4830290 A s t x) (@lem4830320 A s t x)). Qed.
Lemma lem4830324 {A : Type'} (s : type686 A) (t : type686 A) : (term238 A s t) = (term239 A s t).
Proof. exact (fun_ext (fun x : A => @lem4830321 A s t x)). Qed.
Lemma lem4830325 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4830326 {A : Type'} (s : type686 A) (t : type686 A) : (term172 A s t) = (term240 A s t).
Proof. exact (MK_COMB (@lem4830325 A) (@lem4830324 A s t)). Qed.
Lemma lem4830331 {A : Type'} (s : type686 A) (t : type686 A) : (term173 A s t) = (term241 A s t).
Proof. exact (MK_COMB (@lem4830196 A s t) (@lem4830326 A s t)). Qed.
Lemma lem4830334 {A : Type'} (s : type686 A) (t : type686 A) : (term241 A s t) = (term173 A s t).
Proof. exact (SYM (@lem4830331 A s t)). Qed.
Lemma lem4830335 {A : Type'} (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term195 A s t.
Proof. exact (h1). Qed.
Lemma lem4830343 {A : Type'} (P : Prop) (Q : A -> Prop) : (term18 A P Q) = (term19 A P Q).
Proof. exact (EQ_MP (@lem4829828 A P Q) (@lem4829827 A P Q)). Qed.
Lemma lem4830344 {A : Type'} (P : Prop) (Q : type686 A) : (term242 A P Q) = (term243 A P Q).
Proof. exact (@lem4830343 (A -> Prop) P Q). Qed.
Lemma lem4830345 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term244 A s t x z) = (term245 A s t x z).
Proof. exact (@lem4830344 A (@IN (A -> Prop) x s) (term221 A t x z)). Qed.
Lemma lem4830346 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term246 A t x z x') = (term220 A t x z x').
Proof. exact (eq_refl (term246 A t x z x')). Qed.
Lemma lem4830347 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term247 A t x z) = (term221 A t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830346 A t x z x')). Qed.
Lemma lem4830348 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830349 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term248 A t x z) = (term222 A t x z).
Proof. exact (MK_COMB (@lem4830348 A) (@lem4830347 A t x z)). Qed.
Lemma lem4830350 {A : Type'} (x : A -> Prop) (s : type686 A) : (term118 A x s) = (term118 A x s).
Proof. exact (eq_refl (term118 A x s)). Qed.
Lemma lem4830351 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term244 A s t x z) = (term223 A s t x z).
Proof. exact (MK_COMB (@lem4830350 A x s) (@lem4830349 A t x z)). Qed.
Lemma lem4830352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4830353 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term249 A s t x z) = (term250 A s t x z).
Proof. exact (MK_COMB (@lem4830352) (@lem4830351 A s t x z)). Qed.
Lemma lem4830354 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term246 A t x z x') = (term220 A t x z x').
Proof. exact (eq_refl (term246 A t x z x')). Qed.
Lemma lem4830355 {A : Type'} (x : A -> Prop) (s : type686 A) : (term118 A x s) = (term118 A x s).
Proof. exact (eq_refl (term118 A x s)). Qed.
Lemma lem4830356 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term251 A s t x z x') = (term252 A s t x z x').
Proof. exact (MK_COMB (@lem4830355 A x s) (@lem4830354 A t x z x')). Qed.
Lemma lem4830357 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term253 A s t x z) = (term254 A s t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830356 A s t x z x')). Qed.
Lemma lem4830358 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830359 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term245 A s t x z) = (term255 A s t x z).
Proof. exact (MK_COMB (@lem4830358 A) (@lem4830357 A s t x z)). Qed.
Lemma lem4830360 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : ((term244 A s t x z) = (term245 A s t x z)) = ((term223 A s t x z) = (term255 A s t x z)).
Proof. exact (MK_COMB (@lem4830353 A s t x z) (@lem4830359 A s t x z)). Qed.
Lemma lem4830361 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term223 A s t x z) = (term255 A s t x z).
Proof. exact (EQ_MP (@lem4830360 A s t x z) (@lem4830345 A s t x z)). Qed.
Lemma lem4830372 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term224 A s t z) = (term256 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830361 A s t x z)). Qed.
Lemma lem4830373 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830374 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term225 A s t z) = (term257 A s t z).
Proof. exact (MK_COMB (@lem4830373 A) (@lem4830372 A s t z)). Qed.
Lemma lem4830379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4830380 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term226 A s t z) = (term258 A s t z).
Proof. exact (MK_COMB (@lem4830379) (@lem4830374 A s t z)). Qed.
Lemma lem4830389 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (eq_refl (term237 A s t z)). Qed.
Lemma lem4830390 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : ((term225 A s t z) = (term237 A s t z)) = ((term257 A s t z) = (term237 A s t z)).
Proof. exact (MK_COMB (@lem4830380 A s t z) (@lem4830389 A s t z)). Qed.
Lemma lem4830393 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : ((term257 A s t z) = (term237 A s t z)) = ((term225 A s t z) = (term237 A s t z)).
Proof. exact (SYM (@lem4830390 A s t z)). Qed.
Lemma lem4830395 {A : Type'} (P : A -> Prop) (Q : Prop) : (term13 A P Q) = (term14 A P Q).
Proof. exact (EQ_MP (@lem4829822 A P Q) (@lem4829821 A P Q)). Qed.
Lemma lem4830396 {A : Type'} (P : type686 A) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem4830395 (A -> Prop) P Q). Qed.
Lemma lem4830397 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term261 A s t z) = (term262 A s t z).
Proof. exact (@lem4830396 A (term256 A s t z) (term237 A s t z)). Qed.
Lemma lem4830398 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term263 A s t z x) = (term255 A s t x z).
Proof. exact (eq_refl (term263 A s t z x)). Qed.
Lemma lem4830399 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term264 A s t z) = (term256 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830398 A s t x z)). Qed.
Lemma lem4830400 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830401 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term265 A s t z) = (term257 A s t z).
Proof. exact (MK_COMB (@lem4830400 A) (@lem4830399 A s t z)). Qed.
Lemma lem4830402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4830403 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term266 A s t z) = (term267 A s t z).
Proof. exact (MK_COMB (@lem4830402) (@lem4830401 A s t z)). Qed.
Lemma lem4830404 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (eq_refl (term237 A s t z)). Qed.
Lemma lem4830405 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term261 A s t z) = (term268 A s t z).
Proof. exact (MK_COMB (@lem4830403 A s t z) (@lem4830404 A s t z)). Qed.
Lemma lem4830406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4830407 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term269 A s t z) = (term270 A s t z).
Proof. exact (MK_COMB (@lem4830406) (@lem4830405 A s t z)). Qed.
Lemma lem4830408 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term263 A s t z x) = (term255 A s t x z).
Proof. exact (eq_refl (term263 A s t z x)). Qed.
Lemma lem4830409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4830410 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term271 A s t z x) = (term272 A s t x z).
Proof. exact (MK_COMB (@lem4830409) (@lem4830408 A s t x z)). Qed.
Lemma lem4830411 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (eq_refl (term237 A s t z)). Qed.
Lemma lem4830412 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term273 A x s t z) = (term274 A x s t z).
Proof. exact (MK_COMB (@lem4830410 A s t x z) (@lem4830411 A s t z)). Qed.
Lemma lem4830413 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term275 A s t z) = (term276 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830412 A x s t z)). Qed.
Lemma lem4830414 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4830415 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term262 A s t z) = (term277 A s t z).
Proof. exact (MK_COMB (@lem4830414 A) (@lem4830413 A s t z)). Qed.
Lemma lem4830416 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : ((term261 A s t z) = (term262 A s t z)) = ((term268 A s t z) = (term277 A s t z)).
Proof. exact (MK_COMB (@lem4830407 A s t z) (@lem4830415 A s t z)). Qed.
Lemma lem4830417 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term268 A s t z) = (term277 A s t z).
Proof. exact (EQ_MP (@lem4830416 A s t z) (@lem4830397 A s t z)). Qed.
Lemma lem4830423 {A : Type'} (P : A -> Prop) (Q : Prop) : (term13 A P Q) = (term14 A P Q).
Proof. exact (EQ_MP (@lem4829822 A P Q) (@lem4829821 A P Q)). Qed.
Lemma lem4830424 {A : Type'} (P : type686 A) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem4830423 (A -> Prop) P Q). Qed.
Lemma lem4830425 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term278 A x s t z) = (term279 A x s t z).
Proof. exact (@lem4830424 A (term254 A s t x z) (term237 A s t z)). Qed.
Lemma lem4830426 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term280 A s t x z x') = (term252 A s t x z x').
Proof. exact (eq_refl (term280 A s t x z x')). Qed.
Lemma lem4830427 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term281 A s t x z) = (term254 A s t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830426 A s t x z x')). Qed.
Lemma lem4830428 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830429 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term282 A s t x z) = (term255 A s t x z).
Proof. exact (MK_COMB (@lem4830428 A) (@lem4830427 A s t x z)). Qed.
Lemma lem4830430 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4830431 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term283 A s t x z) = (term272 A s t x z).
Proof. exact (MK_COMB (@lem4830430) (@lem4830429 A s t x z)). Qed.
Lemma lem4830432 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (eq_refl (term237 A s t z)). Qed.
Lemma lem4830433 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term278 A x s t z) = (term274 A x s t z).
Proof. exact (MK_COMB (@lem4830431 A s t x z) (@lem4830432 A s t z)). Qed.
Lemma lem4830434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4830435 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term284 A x s t z) = (term285 A x s t z).
Proof. exact (MK_COMB (@lem4830434) (@lem4830433 A x s t z)). Qed.
Lemma lem4830436 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term280 A s t x z x') = (term252 A s t x z x').
Proof. exact (eq_refl (term280 A s t x z x')). Qed.
Lemma lem4830437 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4830438 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term286 A s t x z x') = (term287 A s t x z x').
Proof. exact (MK_COMB (@lem4830437) (@lem4830436 A s t x z x')). Qed.
Lemma lem4830439 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (eq_refl (term237 A s t z)). Qed.
Lemma lem4830440 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term288 A x x' s t z) = (term289 A x x' s t z).
Proof. exact (MK_COMB (@lem4830438 A s t x z x') (@lem4830439 A s t z)). Qed.
Lemma lem4830441 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term290 A x s t z) = (term291 A x s t z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830440 A x x' s t z)). Qed.
Lemma lem4830442 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4830443 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term279 A x s t z) = (term292 A x s t z).
Proof. exact (MK_COMB (@lem4830442 A) (@lem4830441 A x s t z)). Qed.
Lemma lem4830444 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : ((term278 A x s t z) = (term279 A x s t z)) = ((term274 A x s t z) = (term292 A x s t z)).
Proof. exact (MK_COMB (@lem4830435 A x s t z) (@lem4830443 A x s t z)). Qed.
Lemma lem4830445 {A : Type'} (x : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term274 A x s t z) = (term292 A x s t z).
Proof. exact (EQ_MP (@lem4830444 A x s t z) (@lem4830425 A x s t z)). Qed.
Lemma lem4830466 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term276 A s t z) = (term293 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830445 A x s t z)). Qed.
Lemma lem4830467 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4830468 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term277 A s t z) = (term294 A s t z).
Proof. exact (MK_COMB (@lem4830467 A) (@lem4830466 A s t z)). Qed.
Lemma lem4830473 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term268 A s t z) = (term294 A s t z).
Proof. exact (TRANS (@lem4830417 A s t z) (@lem4830468 A s t z)). Qed.
Lemma lem4830474 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term294 A s t z) = (term268 A s t z).
Proof. exact (SYM (@lem4830473 A s t z)). Qed.
Lemma lem4830476 (p : Prop) : p = (term295 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4830477 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term296 A s t z) = (term297 A s t z).
Proof. exact (@lem4830476 (term296 A s t z)). Qed.
Lemma lem4830478 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term297 A s t z) = (term296 A s t z).
Proof. exact (SYM (@lem4830477 A s t z)). Qed.
Lemma lem4830479 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term298 A s t z) : term298 A s t z.
Proof. exact (h1). Qed.
Lemma lem4830482 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term297 A s t z) : term297 A s t z.
Proof. exact (h1). Qed.
Lemma lem4830483 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term299 A s t z.
Proof. exact (fun h0 : term297 A s t z => @lem4830482 A s t z h0). Qed.
Lemma lem4830484 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term299 A s t z) : term299 A s t z.
Proof. exact (h1). Qed.
Lemma lem4830485 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term297 A s t z) : term297 A s t z.
Proof. exact (h1). Qed.
Lemma lem4830486 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term297 A s t z) (h2 : term299 A s t z) : term297 A s t z.
Proof. exact (@lem4830484 A s t z h2 (@lem4830485 A s t z h1)). Qed.
Lemma lem4830487 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term297 A s t z) : term300 A s t z.
Proof. exact (fun h0 : term299 A s t z => @lem4830486 A s t z h1 h0). Qed.
Lemma lem4830488 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term299 A s t z) : term299 A s t z.
Proof. exact (h1). Qed.
Lemma lem4830489 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term297 A s t z) (h2 : term299 A s t z) : term297 A s t z.
Proof. exact (@lem4830487 A s t z h1 (@lem4830488 A s t z h2)). Qed.
Lemma lem4830490 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term299 A s t z) : term299 A s t z.
Proof. exact (fun h0 : term297 A s t z => @lem4830489 A s t z h0 h1). Qed.
Lemma lem4830491 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term301 A s t z.
Proof. exact (fun h0 : term299 A s t z => @lem4830490 A s t z h0). Qed.
Lemma lem4830494 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term299 A s t z.
Proof. exact (@lem4830491 A s t z (@lem4830483 A s t z)). Qed.
Lemma lem4830495 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term299 A s t z.
Proof. exact (@lem4830494 A s t z). Qed.
Lemma lem4830509 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4830510 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term297 A s t z) = (term302 A s t z).
Proof. exact (@lem4830509 (term298 A s t z)). Qed.
Lemma lem4830512 (t : Prop) : (term303 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4830513 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term302 A s t z) = (term296 A s t z).
Proof. exact (@lem4830512 (term296 A s t z)). Qed.
Lemma lem4830516 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term297 A s t z) = (term296 A s t z).
Proof. exact (TRANS (@lem4830510 A s t z) (@lem4830513 A s t z)). Qed.
Lemma lem4830574 {A : Type'} (P : Prop) (Q : A -> Prop) : (term19 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem4830575 {A : Type'} (P : Prop) (Q : type686 A) : (term243 A P Q) = (term242 A P Q).
Proof. exact (@lem4830574 (A -> Prop) P Q). Qed.
Lemma lem4830576 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term245 A s t x z) = (term244 A s t x z).
Proof. exact (@lem4830575 A (@IN (A -> Prop) x s) (term221 A t x z)). Qed.
Lemma lem4830577 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term246 A t x z x') = (term220 A t x z x').
Proof. exact (eq_refl (term246 A t x z x')). Qed.
Lemma lem4830578 {A : Type'} (x : A -> Prop) (s : type686 A) : (term118 A x s) = (term118 A x s).
Proof. exact (eq_refl (term118 A x s)). Qed.
Lemma lem4830579 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term251 A s t x z x') = (term252 A s t x z x').
Proof. exact (MK_COMB (@lem4830578 A x s) (@lem4830577 A t x z x')). Qed.
Lemma lem4830580 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term253 A s t x z) = (term254 A s t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830579 A s t x z x')). Qed.
Lemma lem4830581 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830582 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term245 A s t x z) = (term255 A s t x z).
Proof. exact (MK_COMB (@lem4830581 A) (@lem4830580 A s t x z)). Qed.
Lemma lem4830583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4830584 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term304 A s t x z) = (term305 A s t x z).
Proof. exact (MK_COMB (@lem4830583) (@lem4830582 A s t x z)). Qed.
Lemma lem4830585 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term246 A t x z x') = (term220 A t x z x').
Proof. exact (eq_refl (term246 A t x z x')). Qed.
Lemma lem4830586 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term247 A t x z) = (term221 A t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830585 A t x z x')). Qed.
Lemma lem4830587 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830588 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term248 A t x z) = (term222 A t x z).
Proof. exact (MK_COMB (@lem4830587 A) (@lem4830586 A t x z)). Qed.
Lemma lem4830589 {A : Type'} (x : A -> Prop) (s : type686 A) : (term118 A x s) = (term118 A x s).
Proof. exact (eq_refl (term118 A x s)). Qed.
Lemma lem4830590 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term244 A s t x z) = (term223 A s t x z).
Proof. exact (MK_COMB (@lem4830589 A x s) (@lem4830588 A t x z)). Qed.
Lemma lem4830591 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : ((term245 A s t x z) = (term244 A s t x z)) = ((term255 A s t x z) = (term223 A s t x z)).
Proof. exact (MK_COMB (@lem4830584 A s t x z) (@lem4830590 A s t x z)). Qed.
Lemma lem4830592 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term255 A s t x z) = (term223 A s t x z).
Proof. exact (EQ_MP (@lem4830591 A s t x z) (@lem4830576 A s t x z)). Qed.
Lemma lem4830647 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term256 A s t z) = (term224 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830592 A s t x z)). Qed.
Lemma lem4830648 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830649 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term257 A s t z) = (term225 A s t z).
Proof. exact (MK_COMB (@lem4830648 A) (@lem4830647 A s t z)). Qed.
Lemma lem4830698 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term306 A s t z) = (term306 A s t z).
Proof. exact (eq_refl (term306 A s t z)). Qed.
Lemma lem4830699 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term296 A s t z) = (term307 A s t z).
Proof. exact (MK_COMB (@lem4830698 A s t z) (@lem4830649 A s t z)). Qed.
Lemma lem4830702 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term297 A s t z) = (term307 A s t z).
Proof. exact (TRANS (@lem4830516 A s t z) (@lem4830699 A s t z)). Qed.
Lemma lem4830703 {A : Type'} (t : type686 A) (z : A) : (term308 A t z) = (term309 A t z).
Proof. exact (fun_ext (fun s : type686 A => @lem4830702 A s t z)). Qed.
Lemma lem4830704 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4830705 {A : Type'} (t : type686 A) (z : A) : (term310 A t z) = (term311 A t z).
Proof. exact (MK_COMB (@lem4830704 A) (@lem4830703 A t z)). Qed.
Lemma lem4830710 {A : Type'} (z : A) : (term312 A z) = (term313 A z).
Proof. exact (fun_ext (fun t : type686 A => @lem4830705 A t z)). Qed.
Lemma lem4830711 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4830712 {A : Type'} (z : A) : (term314 A z) = (term315 A z).
Proof. exact (MK_COMB (@lem4830711 A) (@lem4830710 A z)). Qed.
Lemma lem4830717 {A : Type'} : (term316 A) = (term317 A).
Proof. exact (fun_ext (fun z : A => @lem4830712 A z)). Qed.
Lemma lem4830718 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4830727 {A : Type'} : (term318 A) = (term319 A).
Proof. exact (MK_COMB (@lem4830718 A) (@lem4830717 A)). Qed.
Lemma lem4830736 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term220 A t x z x') = (term220 A t x z x').
Proof. exact (eq_refl (term220 A t x z x')). Qed.
Lemma lem4830737 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term221 A t x z) = (term221 A t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830736 A t x z x')). Qed.
Lemma lem4830738 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830739 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term222 A t x z) = (term222 A t x z).
Proof. exact (MK_COMB (@lem4830738 A) (@lem4830737 A t x z)). Qed.
Lemma lem4830742 {A : Type'} (x : A -> Prop) (s : type686 A) : (term118 A x s) = (term118 A x s).
Proof. exact (eq_refl (term118 A x s)). Qed.
Lemma lem4830743 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term223 A s t x z) = (term223 A s t x z).
Proof. exact (MK_COMB (@lem4830742 A x s) (@lem4830739 A t x z)). Qed.
Lemma lem4830744 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term224 A s t z) = (term224 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830743 A s t x z)). Qed.
Lemma lem4830745 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830746 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term225 A s t z) = (term225 A s t z).
Proof. exact (MK_COMB (@lem4830745 A) (@lem4830744 A s t z)). Qed.
Lemma lem4830755 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term234 A s t z t') = (term234 A s t z t').
Proof. exact (eq_refl (term234 A s t z t')). Qed.
Lemma lem4830756 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term236 A s t z) = (term236 A s t z).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4830755 A s t z t')). Qed.
Lemma lem4830757 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830758 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (MK_COMB (@lem4830757 A) (@lem4830756 A s t z)). Qed.
Lemma lem4830759 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4830760 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term306 A s t z) = (term306 A s t z).
Proof. exact (MK_COMB (@lem4830759) (@lem4830758 A s t z)). Qed.
Lemma lem4830761 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term307 A s t z) = (term307 A s t z).
Proof. exact (MK_COMB (@lem4830760 A s t z) (@lem4830746 A s t z)). Qed.
Lemma lem4830762 {A : Type'} (t : type686 A) (z : A) : (term309 A t z) = (term309 A t z).
Proof. exact (fun_ext (fun s : type686 A => @lem4830761 A s t z)). Qed.
Lemma lem4830763 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4830764 {A : Type'} (t : type686 A) (z : A) : (term311 A t z) = (term311 A t z).
Proof. exact (MK_COMB (@lem4830763 A) (@lem4830762 A t z)). Qed.
Lemma lem4830765 {A : Type'} (z : A) : (term313 A z) = (term313 A z).
Proof. exact (fun_ext (fun t : type686 A => @lem4830764 A t z)). Qed.
Lemma lem4830766 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4830767 {A : Type'} (z : A) : (term315 A z) = (term315 A z).
Proof. exact (MK_COMB (@lem4830766 A) (@lem4830765 A z)). Qed.
Lemma lem4830768 {A : Type'} : (term317 A) = (term317 A).
Proof. exact (fun_ext (fun z : A => @lem4830767 A z)). Qed.
Lemma lem4830769 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4830770 {A : Type'} : (term319 A) = (term319 A).
Proof. exact (MK_COMB (@lem4830769 A) (@lem4830768 A)). Qed.
Lemma lem4830821 {A : Type'} : (term318 A) = (term319 A).
Proof. exact (TRANS (@lem4830727 A) (@lem4830770 A)). Qed.
Lemma lem4830822 {A : Type'} : (term319 A) = (term318 A).
Proof. exact (SYM (@lem4830821 A)). Qed.
Lemma lem4830823 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) : term237 A s t z.
Proof. exact (h1). Qed.
Lemma lem4830825 (p : Prop) : p = (term295 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4830826 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term225 A s t z) = (term320 A s t z).
Proof. exact (@lem4830825 (term225 A s t z)). Qed.
Lemma lem4830827 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term320 A s t z) = (term225 A s t z).
Proof. exact (SYM (@lem4830826 A s t z)). Qed.
Lemma lem4830828 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term321 A s t z.
Proof. exact (h1). Qed.
Lemma lem4830837 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term234 A s t z t') = (term234 A s t z t').
Proof. exact (eq_refl (term234 A s t z t')). Qed.
Lemma lem4830838 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term236 A s t z) = (term236 A s t z).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4830837 A s t z t')). Qed.
Lemma lem4830839 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4830892 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (MK_COMB (@lem4830839 A) (@lem4830838 A s t z)). Qed.
Lemma lem4830893 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) : term237 A s t z.
Proof. exact (EQ_MP (@lem4830892 A s t z) (@lem4830823 A s t z h1)). Qed.
Lemma lem4830902 {A : Type'} (x : A -> Prop) (z : A) (x' : A -> Prop) : (term322 A x z x') = (term323 A x z x').
Proof. exact (@lem17045 (@IN A z x) (@IN A z x')). Qed.
Lemma lem4830904 {A : Type'} (x' : A -> Prop) (t : type686 A) : (term324 A x' t) = (term324 A x' t).
Proof. exact (eq_refl (term324 A x' t)). Qed.
Lemma lem4830905 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term325 A t x z x') = (term326 A t x z x').
Proof. exact (MK_COMB (@lem4830904 A x' t) (@lem4830902 A x z x')). Qed.
Lemma lem4830906 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term327 A t x z x') = (term325 A t x z x').
Proof. exact (@lem17045 (@IN (A -> Prop) x' t) (term38 A x z x')). Qed.
Lemma lem4830907 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term327 A t x z x') = (term326 A t x z x').
Proof. exact (TRANS (@lem4830906 A t x z x') (@lem4830905 A t x z x')). Qed.
Lemma lem4830908 {A : Type'} (P : type686 A) : (term328 A P) = (term329 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4830909 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term330 A t x z) = (term331 A t x z).
Proof. exact (@lem4830908 A (term221 A t x z)). Qed.
Lemma lem4830910 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term246 A t x z x') = (term220 A t x z x').
Proof. exact (eq_refl (term246 A t x z x')). Qed.
Lemma lem4830911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4830912 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term332 A t x z x') = (term327 A t x z x').
Proof. exact (MK_COMB (@lem4830911) (@lem4830910 A t x z x')). Qed.
Lemma lem4830913 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term332 A t x z x') = (term326 A t x z x').
Proof. exact (TRANS (@lem4830912 A t x z x') (@lem4830907 A t x z x')). Qed.
Lemma lem4830914 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term333 A t x z) = (term334 A t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4830913 A t x z x')). Qed.
Lemma lem4830915 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4830916 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term331 A t x z) = (term335 A t x z).
Proof. exact (MK_COMB (@lem4830915 A) (@lem4830914 A t x z)). Qed.
Lemma lem4830917 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term330 A t x z) = (term335 A t x z).
Proof. exact (TRANS (@lem4830909 A t x z) (@lem4830916 A t x z)). Qed.
Lemma lem4830919 {A : Type'} (x : A -> Prop) (s : type686 A) : (term324 A x s) = (term324 A x s).
Proof. exact (eq_refl (term324 A x s)). Qed.
Lemma lem4830920 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term336 A s t x z) = (term337 A s t x z).
Proof. exact (MK_COMB (@lem4830919 A x s) (@lem4830917 A t x z)). Qed.
Lemma lem4830921 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term338 A s t x z) = (term336 A s t x z).
Proof. exact (@lem17045 (@IN (A -> Prop) x s) (term222 A t x z)). Qed.
Lemma lem4830922 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term338 A s t x z) = (term337 A s t x z).
Proof. exact (TRANS (@lem4830921 A s t x z) (@lem4830920 A s t x z)). Qed.
Lemma lem4830923 {A : Type'} (P : type686 A) : (term328 A P) = (term329 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4830924 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term321 A s t z) = (term339 A s t z).
Proof. exact (@lem4830923 A (term224 A s t z)). Qed.
Lemma lem4830925 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term340 A s t z x) = (term223 A s t x z).
Proof. exact (eq_refl (term340 A s t z x)). Qed.
Lemma lem4830926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4830927 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term341 A s t z x) = (term338 A s t x z).
Proof. exact (MK_COMB (@lem4830926) (@lem4830925 A s t x z)). Qed.
Lemma lem4830928 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term341 A s t z x) = (term337 A s t x z).
Proof. exact (TRANS (@lem4830927 A s t x z) (@lem4830922 A s t x z)). Qed.
Lemma lem4830929 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term342 A s t z) = (term343 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4830928 A s t x z)). Qed.
Lemma lem4830930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4830931 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term339 A s t z) = (term344 A s t z).
Proof. exact (MK_COMB (@lem4830930 A) (@lem4830929 A s t z)). Qed.
Lemma lem4831032 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term321 A s t z) = (term344 A s t z).
Proof. exact (TRANS (@lem4830924 A s t z) (@lem4830931 A s t z)). Qed.
Lemma lem4831033 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term344 A s t z.
Proof. exact (EQ_MP (@lem4831032 A s t z) (@lem4830828 A s t z h1)). Qed.
Lemma lem4831061 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term326 A t x z x') = (term326 A t x z x').
Proof. exact (eq_refl (term326 A t x z x')). Qed.
Lemma lem4831062 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term334 A t x z) = (term334 A t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4831061 A t x z x')). Qed.
Lemma lem4831063 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831064 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term335 A t x z) = (term335 A t x z).
Proof. exact (MK_COMB (@lem4831063 A) (@lem4831062 A t x z)). Qed.
Lemma lem4831073 {A : Type'} (x : A -> Prop) (s : type686 A) : (term324 A x s) = (term324 A x s).
Proof. exact (eq_refl (term324 A x s)). Qed.
Lemma lem4831074 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term337 A s t x z) = (term337 A s t x z).
Proof. exact (MK_COMB (@lem4831073 A x s) (@lem4831064 A t x z)). Qed.
Lemma lem4831075 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term343 A s t z) = (term343 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4831074 A s t x z)). Qed.
Lemma lem4831076 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831077 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term344 A s t z) = (term344 A s t z).
Proof. exact (MK_COMB (@lem4831076 A) (@lem4831075 A s t z)). Qed.
Lemma lem4831078 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term344 A s t z.
Proof. exact (EQ_MP (@lem4831077 A s t z) (@lem4831033 A s t z h1)). Qed.
Lemma lem4831100 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term234 A s t z t'.
Proof. exact (h1). Qed.
Lemma lem4831102 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term230 A s t' t.
Proof. exact (proj1 (@lem4831100 A s t z t' h1)). Qed.
Lemma lem4831106 {A : Type'} (P : Prop) (Q : A -> Prop) : (term345 A P Q) = (term346 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4831107 {A : Type'} (P : Prop) (Q : type686 A) : (term347 A P Q) = (term348 A P Q).
Proof. exact (@lem4831106 (A -> Prop) P Q). Qed.
Lemma lem4831108 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term349 A s t x z) = (term350 A s t x z).
Proof. exact (@lem4831107 A (term351 A x s) (term334 A t x z)). Qed.
Lemma lem4831109 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term352 A t x z x') = (term326 A t x z x').
Proof. exact (eq_refl (term352 A t x z x')). Qed.
Lemma lem4831110 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term353 A t x z) = (term334 A t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4831109 A t x z x')). Qed.
Lemma lem4831111 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831112 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) : (term354 A t x z) = (term335 A t x z).
Proof. exact (MK_COMB (@lem4831111 A) (@lem4831110 A t x z)). Qed.
Lemma lem4831113 {A : Type'} (x : A -> Prop) (s : type686 A) : (term324 A x s) = (term324 A x s).
Proof. exact (eq_refl (term324 A x s)). Qed.
Lemma lem4831114 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term349 A s t x z) = (term337 A s t x z).
Proof. exact (MK_COMB (@lem4831113 A x s) (@lem4831112 A t x z)). Qed.
Lemma lem4831115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4831116 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term355 A s t x z) = (term356 A s t x z).
Proof. exact (MK_COMB (@lem4831115) (@lem4831114 A s t x z)). Qed.
Lemma lem4831117 {A : Type'} (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term352 A t x z x') = (term326 A t x z x').
Proof. exact (eq_refl (term352 A t x z x')). Qed.
Lemma lem4831118 {A : Type'} (x : A -> Prop) (s : type686 A) : (term324 A x s) = (term324 A x s).
Proof. exact (eq_refl (term324 A x s)). Qed.
Lemma lem4831119 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term357 A s t x z x') = (term358 A s t x z x').
Proof. exact (MK_COMB (@lem4831118 A x s) (@lem4831117 A t x z x')). Qed.
Lemma lem4831120 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term359 A s t x z) = (term360 A s t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4831119 A s t x z x')). Qed.
Lemma lem4831121 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831122 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term350 A s t x z) = (term361 A s t x z).
Proof. exact (MK_COMB (@lem4831121 A) (@lem4831120 A s t x z)). Qed.
Lemma lem4831123 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : ((term349 A s t x z) = (term350 A s t x z)) = ((term337 A s t x z) = (term361 A s t x z)).
Proof. exact (MK_COMB (@lem4831116 A s t x z) (@lem4831122 A s t x z)). Qed.
Lemma lem4831124 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term337 A s t x z) = (term361 A s t x z).
Proof. exact (EQ_MP (@lem4831123 A s t x z) (@lem4831108 A s t x z)). Qed.
Lemma lem4831125 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term343 A s t z) = (term362 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4831124 A s t x z)). Qed.
Lemma lem4831126 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831127 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term344 A s t z) = (term363 A s t z).
Proof. exact (MK_COMB (@lem4831126 A) (@lem4831125 A s t z)). Qed.
Lemma lem4831146 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) (x' : A -> Prop) : (term358 A s t x z x') = (term358 A s t x z x').
Proof. exact (eq_refl (term358 A s t x z x')). Qed.
Lemma lem4831147 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term360 A s t x z) = (term360 A s t x z).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4831146 A s t x z x')). Qed.
Lemma lem4831148 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831149 {A : Type'} (s : type686 A) (t : type686 A) (x : A -> Prop) (z : A) : (term361 A s t x z) = (term361 A s t x z).
Proof. exact (MK_COMB (@lem4831148 A) (@lem4831147 A s t x z)). Qed.
Lemma lem4831150 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term362 A s t z) = (term362 A s t z).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4831149 A s t x z)). Qed.
Lemma lem4831151 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831152 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term363 A s t z) = (term363 A s t z).
Proof. exact (MK_COMB (@lem4831151 A) (@lem4831150 A s t z)). Qed.
Lemma lem4831153 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term344 A s t z) = (term363 A s t z).
Proof. exact (TRANS (@lem4831127 A s t z) (@lem4831152 A s t z)). Qed.
Lemma lem4831154 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term363 A s t z.
Proof. exact (EQ_MP (@lem4831153 A s t z) (@lem4831078 A s t z h1)). Qed.
Lemma lem4831167 {A : Type'} (_59840 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term364 A s t z _59840.
Proof. exact (@lem4831154 A s t z h1 _59840). Qed.
Lemma lem4831168 {A : Type'} (s : type686 A) (t : type686 A) (_59840 : A -> Prop) (z : A) : (term364 A s t z _59840) = (term361 A s t _59840 z).
Proof. exact (eq_refl (term364 A s t z _59840)). Qed.
Lemma lem4831169 {A : Type'} (_59840 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term361 A s t _59840 z.
Proof. exact (EQ_MP (@lem4831168 A s t _59840 z) (@lem4831167 A _59840 s t z h1)). Qed.
Lemma lem4831170 {A : Type'} (_59840 : A -> Prop) (_59841 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term365 A s t _59840 z _59841.
Proof. exact (@lem4831169 A _59840 s t z h1 _59841). Qed.
Lemma lem4831171 {A : Type'} (s : type686 A) (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term365 A s t _59840 z _59841) = (term358 A s t _59840 z _59841).
Proof. exact (eq_refl (term365 A s t _59840 z _59841)). Qed.
Lemma lem4831186 {A : Type'} (_59840 : A -> Prop) (_59841 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term358 A s t _59840 z _59841.
Proof. exact (EQ_MP (@lem4831171 A s t _59840 z _59841) (@lem4831170 A _59840 _59841 s t z h1)). Qed.
Lemma lem4831194 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : @IN (A -> Prop) t' s.
Proof. exact (proj1 (@lem4831102 A s t z t' h1)). Qed.
Lemma lem4831195 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term366 A t' s.
Proof. exact (fun h0 : term351 A t' s => @lem4831194 A s t z t' h1). Qed.
Lemma lem4831197 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4831198 {A : Type'} (t' : A -> Prop) (s : type686 A) : (term366 A t' s) = (@IN (A -> Prop) t' s).
Proof. exact (@lem4831197 (@IN (A -> Prop) t' s)). Qed.
Lemma lem4831199 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : @IN (A -> Prop) t' s.
Proof. exact (EQ_MP (@lem4831198 A t' s) (@lem4831195 A s t z t' h1)). Qed.
Lemma lem4831201 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : @IN (A -> Prop) t' t.
Proof. exact (proj2 (@lem4831102 A s t z t' h1)). Qed.
Lemma lem4831202 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term366 A t' t.
Proof. exact (fun h0 : term351 A t' t => @lem4831201 A s t z t' h1). Qed.
Lemma lem4831204 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4831205 {A : Type'} (t' : A -> Prop) (t : type686 A) : (term366 A t' t) = (@IN (A -> Prop) t' t).
Proof. exact (@lem4831204 (@IN (A -> Prop) t' t)). Qed.
Lemma lem4831206 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : @IN (A -> Prop) t' t.
Proof. exact (EQ_MP (@lem4831205 A t' t) (@lem4831202 A s t z t' h1)). Qed.
Lemma lem4831208 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : @IN A z t'.
Proof. exact (proj2 (@lem4831100 A s t z t' h1)). Qed.
Lemma lem4831209 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term368 A z t'.
Proof. exact (fun h0 : term369 A z t' => @lem4831208 A s t z t' h1). Qed.
Lemma lem4831211 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4831212 {A : Type'} (z : A) (t' : A -> Prop) : (term368 A z t') = (@IN A z t').
Proof. exact (@lem4831211 (@IN A z t')). Qed.
Lemma lem4831213 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : @IN A z t'.
Proof. exact (EQ_MP (@lem4831212 A z t') (@lem4831209 A s t z t' h1)). Qed.
Lemma lem4831215 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : @IN A z t'.
Proof. exact (proj2 (@lem4831100 A s t z t' h1)). Qed.
Lemma lem4831216 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term368 A z t'.
Proof. exact (fun h0 : term369 A z t' => @lem4831215 A s t z t' h1). Qed.
Lemma lem4831218 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4831219 {A : Type'} (z : A) (t' : A -> Prop) : (term368 A z t') = (@IN A z t').
Proof. exact (@lem4831218 (@IN A z t')). Qed.
Lemma lem4831220 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : @IN A z t'.
Proof. exact (EQ_MP (@lem4831219 A z t') (@lem4831216 A s t z t' h1)). Qed.
Lemma lem4831222 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4831223 {A : Type'} (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term323 A _59840 z _59841) = (term322 A _59840 z _59841).
Proof. exact (@lem4831222 (@IN A z _59840) (@IN A z _59841)). Qed.
Lemma lem4831224 {A : Type'} (_59841 : A -> Prop) (t : type686 A) : (term324 A _59841 t) = (term324 A _59841 t).
Proof. exact (eq_refl (term324 A _59841 t)). Qed.
Lemma lem4831225 {A : Type'} (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term326 A t _59840 z _59841) = (term325 A t _59840 z _59841).
Proof. exact (MK_COMB (@lem4831224 A _59841 t) (@lem4831223 A _59840 z _59841)). Qed.
Lemma lem4831227 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4831228 {A : Type'} (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term325 A t _59840 z _59841) = (term327 A t _59840 z _59841).
Proof. exact (@lem4831227 (@IN (A -> Prop) _59841 t) (term38 A _59840 z _59841)). Qed.
Lemma lem4831229 {A : Type'} (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term326 A t _59840 z _59841) = (term327 A t _59840 z _59841).
Proof. exact (TRANS (@lem4831225 A t _59840 z _59841) (@lem4831228 A t _59840 z _59841)). Qed.
Lemma lem4831230 {A : Type'} (_59840 : A -> Prop) (s : type686 A) : (term324 A _59840 s) = (term324 A _59840 s).
Proof. exact (eq_refl (term324 A _59840 s)). Qed.
Lemma lem4831231 {A : Type'} (s : type686 A) (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term358 A s t _59840 z _59841) = (term372 A s t _59840 z _59841).
Proof. exact (MK_COMB (@lem4831230 A _59840 s) (@lem4831229 A t _59840 z _59841)). Qed.
Lemma lem4831233 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4831234 {A : Type'} (s : type686 A) (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term372 A s t _59840 z _59841) = (term373 A s t _59840 z _59841).
Proof. exact (@lem4831233 (@IN (A -> Prop) _59840 s) (term220 A t _59840 z _59841)). Qed.
Lemma lem4831235 {A : Type'} (s : type686 A) (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term358 A s t _59840 z _59841) = (term373 A s t _59840 z _59841).
Proof. exact (TRANS (@lem4831231 A s t _59840 z _59841) (@lem4831234 A s t _59840 z _59841)). Qed.
Lemma lem4831237 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4831238 {A : Type'} (s : type686 A) (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term373 A s t _59840 z _59841) = (term374 A s t _59840 z _59841).
Proof. exact (@lem4831237 (term252 A s t _59840 z _59841)). Qed.
Lemma lem4831239 {A : Type'} (s : type686 A) (t : type686 A) (_59840 : A -> Prop) (z : A) (_59841 : A -> Prop) : (term358 A s t _59840 z _59841) = (term374 A s t _59840 z _59841).
Proof. exact (TRANS (@lem4831235 A s t _59840 z _59841) (@lem4831238 A s t _59840 z _59841)). Qed.
Lemma lem4831241 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term375 A z t'.
Proof. exact (conj (@lem4831213 A s t z t' h1) (@lem4831220 A s t z t' h1)). Qed.
Lemma lem4831242 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term376 A t z t'.
Proof. exact (conj (@lem4831206 A s t z t' h1) (@lem4831241 A s t z t' h1)). Qed.
Lemma lem4831243 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term234 A s t z t') : term377 A s t z t'.
Proof. exact (conj (@lem4831199 A s t z t' h1) (@lem4831242 A s t z t' h1)). Qed.
Lemma lem4831245 {A : Type'} (_59840 : A -> Prop) (_59841 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term374 A s t _59840 z _59841.
Proof. exact (EQ_MP (@lem4831239 A s t _59840 z _59841) (@lem4831186 A _59840 _59841 s t z h1)). Qed.
Lemma lem4831246 {A : Type'} (_59840 : A -> Prop) (_59841 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term374 A s t _59840 z _59841.
Proof. exact (@lem4831245 A _59840 _59841 s t z h1). Qed.
Lemma lem4831247 {A : Type'} (t' : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term321 A s t z) : term378 A s t z t'.
Proof. exact (@lem4831246 A t' t' s t z h1). Qed.
Lemma lem4831250 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term321 A s t z) (h2 : term234 A s t z t') : False.
Proof. exact (@lem4831247 A t' s t z h1 (@lem4831243 A s t z t' h2)). Qed.
Lemma lem4831251 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term321 A s t z) (h2 : term234 A s t z t') : term379.
Proof. exact (fun h0 : ~ False => @lem4831250 A s t z t' h1 h2). Qed.
Lemma lem4831253 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4831254 : term379 = False.
Proof. exact (@lem4831253 False). Qed.
Lemma lem4831255 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term321 A s t z) (h2 : term234 A s t z t') : False.
Proof. exact (EQ_MP (@lem4831254) (@lem4831251 A s t z t' h1 h2)). Qed.
Lemma lem4831256 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term321 A s t z) (h2 : term234 A s t z t') : (term234 A s t z t') = False.
Proof. exact (prop_ext (fun h3 : term234 A s t z t' => @lem4831255 A s t z t' h1 h2) (fun h3 : False => @lem4831100 A s t z t' h2)). Qed.
Lemma lem4831257 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) (h1 : term321 A s t z) (h2 : term234 A s t z t') : False.
Proof. exact (EQ_MP (@lem4831256 A s t z t' h1 h2) (@lem4831100 A s t z t' h2)). Qed.
Lemma lem4831258 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) (h2 : term321 A s t z) : False.
Proof. exact (ex_elim (@lem4830893 A s t z h1) (fun t' : A -> Prop => fun h0 : term236 A s t z t' => @lem4831257 A s t z t' h2 h0)). Qed.
Lemma lem4831259 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) (h2 : term321 A s t z) : (term237 A s t z) = False.
Proof. exact (prop_ext (fun h3 : term237 A s t z => @lem4831258 A s t z h1 h2) (fun h3 : False => @lem4830893 A s t z h1)). Qed.
Lemma lem4831260 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) (h2 : term321 A s t z) : False.
Proof. exact (EQ_MP (@lem4831259 A s t z h1 h2) (@lem4830893 A s t z h1)). Qed.
Lemma lem4831261 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) (h2 : term321 A s t z) : (term321 A s t z) = False.
Proof. exact (prop_ext (fun h3 : term321 A s t z => @lem4831260 A s t z h1 h2) (fun h3 : False => @lem4830828 A s t z h2)). Qed.
Lemma lem4831262 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) (h2 : term321 A s t z) : False.
Proof. exact (EQ_MP (@lem4831261 A s t z h1 h2) (@lem4830828 A s t z h2)). Qed.
Lemma lem4831263 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) : term320 A s t z.
Proof. exact (fun h0 : term321 A s t z => @lem4831262 A s t z h1 h0). Qed.
Lemma lem4831264 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term237 A s t z) : term225 A s t z.
Proof. exact (EQ_MP (@lem4830827 A s t z) (@lem4831263 A s t z h1)). Qed.
Lemma lem4831265 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term307 A s t z.
Proof. exact (fun h0 : term237 A s t z => @lem4831264 A s t z h0). Qed.
Lemma lem4831270 {A : Type'} (t : type686 A) (z : A) : term311 A t z.
Proof. exact (fun s : type686 A => @lem4831265 A s t z). Qed.
Lemma lem4831275 {A : Type'} (z : A) : term315 A z.
Proof. exact (fun t : type686 A => @lem4831270 A t z). Qed.
Lemma lem4831280 {A : Type'} : term319 A.
Proof. exact (fun z : A => @lem4831275 A z). Qed.
Lemma lem4831281 {A : Type'} : term318 A.
Proof. exact (EQ_MP (@lem4830822 A) (@lem4831280 A)). Qed.
Lemma lem4831282 {A : Type'} (z : A) : term380 A z.
Proof. exact (@lem4831281 A z). Qed.
Lemma lem4831283 {A : Type'} (z : A) : (term380 A z) = (term314 A z).
Proof. exact (eq_refl (term380 A z)). Qed.
Lemma lem4831284 {A : Type'} (z : A) : term314 A z.
Proof. exact (EQ_MP (@lem4831283 A z) (@lem4831282 A z)). Qed.
Lemma lem4831285 {A : Type'} (z : A) (t : type686 A) : term381 A z t.
Proof. exact (@lem4831284 A z t). Qed.
Lemma lem4831286 {A : Type'} (t : type686 A) (z : A) : (term381 A z t) = (term310 A t z).
Proof. exact (eq_refl (term381 A z t)). Qed.
Lemma lem4831287 {A : Type'} (t : type686 A) (z : A) : term310 A t z.
Proof. exact (EQ_MP (@lem4831286 A t z) (@lem4831285 A z t)). Qed.
Lemma lem4831288 {A : Type'} (t : type686 A) (z : A) (s : type686 A) : term382 A t z s.
Proof. exact (@lem4831287 A t z s). Qed.
Lemma lem4831289 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term382 A t z s) = (term297 A s t z).
Proof. exact (eq_refl (term382 A t z s)). Qed.
Lemma lem4831290 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term297 A s t z.
Proof. exact (EQ_MP (@lem4831289 A s t z) (@lem4831288 A t z s)). Qed.
Lemma lem4831292 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term297 A s t z.
Proof. exact (@lem4830495 A s t z (@lem4831290 A s t z)). Qed.
Lemma lem4831293 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term298 A s t z) : False.
Proof. exact (@lem4831292 A s t z (@lem4830479 A s t z h1)). Qed.
Lemma lem4831294 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term298 A s t z) : (term298 A s t z) = False.
Proof. exact (prop_ext (fun h2 : term298 A s t z => @lem4831293 A s t z h1) (fun h2 : False => @lem4830479 A s t z h1)). Qed.
Lemma lem4831295 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term298 A s t z) : False.
Proof. exact (EQ_MP (@lem4831294 A s t z h1) (@lem4830479 A s t z h1)). Qed.
Lemma lem4831296 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term297 A s t z.
Proof. exact (fun h0 : term298 A s t z => @lem4831295 A s t z h0). Qed.
Lemma lem4831297 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term296 A s t z.
Proof. exact (EQ_MP (@lem4830478 A s t z) (@lem4831296 A s t z)). Qed.
Lemma lem4831298 {A : Type'} (s : type686 A) (t : type686 A) (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term252 A s t u z v) : term252 A s t u z v.
Proof. exact (h1). Qed.
Lemma lem4831299 {A : Type'} (t : type686 A) (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term220 A t u z v) : term220 A t u z v.
Proof. exact (h1). Qed.
Lemma lem4831300 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : @IN (A -> Prop) u s.
Proof. exact (h1). Qed.
Lemma lem4831301 {A : Type'} (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term38 A u z v) : term38 A u z v.
Proof. exact (h1). Qed.
Lemma lem4831302 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : @IN (A -> Prop) v t.
Proof. exact (h1). Qed.
Lemma lem4831303 {A : Type'} (z : A) (v : A -> Prop) (h1 : @IN A z v) : @IN A z v.
Proof. exact (h1). Qed.
Lemma lem4831304 {A : Type'} (z : A) (u : A -> Prop) (h1 : @IN A z u) : @IN A z u.
Proof. exact (h1). Qed.
Lemma lem4831305 {A : Type'} (u : A -> Prop) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term383 A s t u.
Proof. exact (@lem4830335 A s t h1 u). Qed.
Lemma lem4831306 {A : Type'} (s : type686 A) (t : type686 A) (u : A -> Prop) : (term383 A s t u) = (term192 A s t u).
Proof. exact (eq_refl (term383 A s t u)). Qed.
Lemma lem4831307 {A : Type'} (u : A -> Prop) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term192 A s t u.
Proof. exact (EQ_MP (@lem4831306 A s t u) (@lem4831305 A u s t h1)). Qed.
Lemma lem4831308 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term384 A s t u v.
Proof. exact (@lem4831307 A u s t h1 v). Qed.
Lemma lem4831309 {A : Type'} (s : type686 A) (t : type686 A) (u : A -> Prop) (v : A -> Prop) : (term384 A s t u v) = (term188 A s t u v).
Proof. exact (eq_refl (term384 A s t u v)). Qed.
Lemma lem4831310 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term188 A s t u v.
Proof. exact (EQ_MP (@lem4831309 A s t u v) (@lem4831308 A u v s t h1)). Qed.
Lemma lem4831311 {A : Type'} (u : A -> Prop) (s : type686 A) : (@IN (A -> Prop) u s) = ((@IN (A -> Prop) u s) = True).
Proof. exact (@lem7 (@IN (A -> Prop) u s)). Qed.
Lemma lem4831313 {A : Type'} (v : A -> Prop) (t : type686 A) : (@IN (A -> Prop) v t) = ((@IN (A -> Prop) v t) = True).
Proof. exact (@lem7 (@IN (A -> Prop) v t)). Qed.
Lemma lem4831328 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : (@IN (A -> Prop) u s) = True.
Proof. exact (EQ_MP (@lem4831311 A u s) (@lem4831300 A u s h1)). Qed.
Lemma lem4831329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4831330 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : (term385 A u s) = (or True).
Proof. exact (MK_COMB (@lem4831329) (@lem4831328 A u s h1)). Qed.
Lemma lem4831332 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : u = v.
Proof. exact (h1). Qed.
Lemma lem4831333 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem4831334 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (@IN (A -> Prop) u) = (@IN (A -> Prop) v).
Proof. exact (MK_COMB (@lem4831333 A) (@lem4831332 A u v h1)). Qed.
Lemma lem4831335 {A : Type'} (t : type686 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4831336 {A : Type'} (t : type686 A) (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (@IN (A -> Prop) u t) = (@IN (A -> Prop) v t).
Proof. exact (MK_COMB (@lem4831334 A u v h1) (@lem4831335 A t)). Qed.
Lemma lem4831338 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = True.
Proof. exact (EQ_MP (@lem4831313 A v t) (@lem4831302 A v t h1)). Qed.
Lemma lem4831339 {A : Type'} (u : A -> Prop) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) v t) : (@IN (A -> Prop) u t) = True.
Proof. exact (TRANS (@lem4831336 A t u v h1) (@lem4831338 A v t h2)). Qed.
Lemma lem4831340 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term178 A s u t) = (True \/ True).
Proof. exact (MK_COMB (@lem4831330 A u s h2) (@lem4831339 A u v t h1 h3)). Qed.
Lemma lem4831342 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4831343 : (True \/ True) = True.
Proof. exact (@lem4831342 True). Qed.
Lemma lem4831344 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term178 A s u t) = True.
Proof. exact (TRANS (@lem4831340 A u s v t h1 h2 h3) (@lem4831343)). Qed.
Lemma lem4831345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4831346 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term180 A s u t) = (and True).
Proof. exact (MK_COMB (@lem4831345) (@lem4831344 A u s v t h1 h2 h3)). Qed.
Lemma lem4831352 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = True.
Proof. exact (EQ_MP (@lem4831313 A v t) (@lem4831302 A v t h1)). Qed.
Lemma lem4831353 {A : Type'} (v : A -> Prop) (s : type686 A) : (term385 A v s) = (term385 A v s).
Proof. exact (eq_refl (term385 A v s)). Qed.
Lemma lem4831354 {A : Type'} (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (term178 A s v t) = (term386 A v s).
Proof. exact (MK_COMB (@lem4831353 A v s) (@lem4831352 A v t h1)). Qed.
Lemma lem4831356 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4831357 {A : Type'} (v : A -> Prop) (s : type686 A) : (term386 A v s) = True.
Proof. exact (@lem4831356 (@IN (A -> Prop) v s)). Qed.
Lemma lem4831358 {A : Type'} (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (term178 A s v t) = True.
Proof. exact (TRANS (@lem4831354 A s v t h1) (@lem4831357 A v s)). Qed.
Lemma lem4831359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4831360 {A : Type'} (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (term180 A s v t) = (and True).
Proof. exact (MK_COMB (@lem4831359) (@lem4831358 A s v t h1)). Qed.
Lemma lem4831364 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : u = v.
Proof. exact (h1). Qed.
Lemma lem4831365 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4831366 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (@eq (A -> Prop) u) = (@eq (A -> Prop) v).
Proof. exact (MK_COMB (@lem4831365 A) (@lem4831364 A u v h1)). Qed.
Lemma lem4831367 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem4831368 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (u = v) = (v = v).
Proof. exact (MK_COMB (@lem4831366 A u v h1) (@lem4831367 A v)). Qed.
Lemma lem4831370 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4831371 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4831370 (A -> Prop) x). Qed.
Lemma lem4831372 {A : Type'} (v : A -> Prop) : (v = v) = True.
Proof. exact (@lem4831371 A v). Qed.
Lemma lem4831373 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (u = v) = True.
Proof. exact (TRANS (@lem4831368 A u v h1) (@lem4831372 A v)). Qed.
Lemma lem4831374 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4831375 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (term9 A u v) = (~ True).
Proof. exact (MK_COMB (@lem4831374) (@lem4831373 A u v h1)). Qed.
Lemma lem4831377 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4831378 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (term9 A u v) = False.
Proof. exact (TRANS (@lem4831375 A u v h1) (@lem4831377)). Qed.
Lemma lem4831379 {A : Type'} (s : type686 A) (u : A -> Prop) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) v t) : (term182 A s t u v) = (True /\ False).
Proof. exact (MK_COMB (@lem4831360 A s v t h2) (@lem4831378 A u v h1)). Qed.
Lemma lem4831381 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4831382 : (True /\ False) = False.
Proof. exact (@lem4831381 False). Qed.
Lemma lem4831383 {A : Type'} (s : type686 A) (u : A -> Prop) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) v t) : (term182 A s t u v) = False.
Proof. exact (TRANS (@lem4831379 A s u v t h1 h2) (@lem4831382)). Qed.
Lemma lem4831384 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term184 A s t u v) = (True /\ False).
Proof. exact (MK_COMB (@lem4831346 A u s v t h1 h2 h3) (@lem4831383 A s u v t h1 h3)). Qed.
Lemma lem4831386 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4831387 : (True /\ False) = False.
Proof. exact (@lem4831386 False). Qed.
Lemma lem4831388 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term184 A s t u v) = False.
Proof. exact (TRANS (@lem4831384 A u s v t h1 h2 h3) (@lem4831387)). Qed.
Lemma lem4831389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4831390 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term186 A s t u v) = (imp False).
Proof. exact (MK_COMB (@lem4831389) (@lem4831388 A u s v t h1 h2 h3)). Qed.
Lemma lem4831392 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : u = v.
Proof. exact (h1). Qed.
Lemma lem4831393 {A : Type'} : (@DISJOINT A) = (@DISJOINT A).
Proof. exact (eq_refl (@DISJOINT A)). Qed.
Lemma lem4831394 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (@DISJOINT A u) = (@DISJOINT A v).
Proof. exact (MK_COMB (@lem4831393 A) (@lem4831392 A u v h1)). Qed.
Lemma lem4831395 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem4831396 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (@DISJOINT A u v) = (@DISJOINT A v v).
Proof. exact (MK_COMB (@lem4831394 A u v h1) (@lem4831395 A v)). Qed.
Lemma lem4831397 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term188 A s t u v) = (term387 A v).
Proof. exact (MK_COMB (@lem4831390 A u s v t h1 h2 h3) (@lem4831396 A u v h1)). Qed.
Lemma lem4831399 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4831400 {A : Type'} (v : A -> Prop) : (term387 A v) = True.
Proof. exact (@lem4831399 (@DISJOINT A v v)). Qed.
Lemma lem4831401 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term188 A s t u v) = True.
Proof. exact (TRANS (@lem4831397 A u s v t h1 h2 h3) (@lem4831400 A v)). Qed.
Lemma lem4831402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4831403 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term388 A s t u v) = (imp True).
Proof. exact (MK_COMB (@lem4831402) (@lem4831401 A u s v t h1 h2 h3)). Qed.
Lemma lem4831412 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (eq_refl (term237 A s t z)). Qed.
Lemma lem4831413 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term389 A u v s t z) = (term390 A s t z).
Proof. exact (MK_COMB (@lem4831403 A u s v t h1 h2 h3) (@lem4831412 A s t z)). Qed.
Lemma lem4831415 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4831416 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term390 A s t z) = (term237 A s t z).
Proof. exact (@lem4831415 (term237 A s t z)). Qed.
Lemma lem4831425 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term389 A u v s t z) = (term237 A s t z).
Proof. exact (TRANS (@lem4831413 A z u s v t h1 h2 h3) (@lem4831416 A s t z)). Qed.
Lemma lem4831426 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term237 A s t z) = (term389 A u v s t z).
Proof. exact (SYM (@lem4831425 A z u s v t h1 h2 h3)). Qed.
Lemma lem4831427 {A : Type'} (u : A -> Prop) (s : type686 A) : (@IN (A -> Prop) u s) = ((@IN (A -> Prop) u s) = True).
Proof. exact (@lem7 (@IN (A -> Prop) u s)). Qed.
Lemma lem4831429 {A : Type'} (v : A -> Prop) (t : type686 A) : (@IN (A -> Prop) v t) = ((@IN (A -> Prop) v t) = True).
Proof. exact (@lem7 (@IN (A -> Prop) v t)). Qed.
Lemma lem4831435 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term391 A u v.
Proof. exact (@lem82 (u = v)). Qed.
Lemma lem4831457 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : (@IN (A -> Prop) u s) = True.
Proof. exact (EQ_MP (@lem4831427 A u s) (@lem4831300 A u s h1)). Qed.
Lemma lem4831458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4831459 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : (term385 A u s) = (or True).
Proof. exact (MK_COMB (@lem4831458) (@lem4831457 A u s h1)). Qed.
Lemma lem4831460 {A : Type'} (u : A -> Prop) (t : type686 A) : (@IN (A -> Prop) u t) = (@IN (A -> Prop) u t).
Proof. exact (eq_refl (@IN (A -> Prop) u t)). Qed.
Lemma lem4831461 {A : Type'} (t : type686 A) (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : (term178 A s u t) = (term392 A u t).
Proof. exact (MK_COMB (@lem4831459 A u s h1) (@lem4831460 A u t)). Qed.
Lemma lem4831463 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4831464 {A : Type'} (u : A -> Prop) (t : type686 A) : (term392 A u t) = True.
Proof. exact (@lem4831463 (@IN (A -> Prop) u t)). Qed.
Lemma lem4831465 {A : Type'} (t : type686 A) (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : (term178 A s u t) = True.
Proof. exact (TRANS (@lem4831461 A t u s h1) (@lem4831464 A u t)). Qed.
Lemma lem4831466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4831467 {A : Type'} (t : type686 A) (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : (term180 A s u t) = (and True).
Proof. exact (MK_COMB (@lem4831466) (@lem4831465 A t u s h1)). Qed.
Lemma lem4831473 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = True.
Proof. exact (EQ_MP (@lem4831429 A v t) (@lem4831302 A v t h1)). Qed.
Lemma lem4831474 {A : Type'} (v : A -> Prop) (s : type686 A) : (term385 A v s) = (term385 A v s).
Proof. exact (eq_refl (term385 A v s)). Qed.
Lemma lem4831475 {A : Type'} (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (term178 A s v t) = (term386 A v s).
Proof. exact (MK_COMB (@lem4831474 A v s) (@lem4831473 A v t h1)). Qed.
Lemma lem4831477 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4831478 {A : Type'} (v : A -> Prop) (s : type686 A) : (term386 A v s) = True.
Proof. exact (@lem4831477 (@IN (A -> Prop) v s)). Qed.
Lemma lem4831479 {A : Type'} (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (term178 A s v t) = True.
Proof. exact (TRANS (@lem4831475 A s v t h1) (@lem4831478 A v s)). Qed.
Lemma lem4831480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4831481 {A : Type'} (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : (term180 A s v t) = (and True).
Proof. exact (MK_COMB (@lem4831480) (@lem4831479 A s v t h1)). Qed.
Lemma lem4831483 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term9 A u v) : (u = v) = False.
Proof. exact (@lem4831435 A u v (@lem4829807 A u v h1)). Qed.
Lemma lem4831484 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4831485 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term9 A u v) : (term9 A u v) = (~ False).
Proof. exact (MK_COMB (@lem4831484) (@lem4831483 A u v h1)). Qed.
Lemma lem4831487 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4831488 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term9 A u v) : (term9 A u v) = True.
Proof. exact (TRANS (@lem4831485 A u v h1) (@lem4831487)). Qed.
Lemma lem4831489 {A : Type'} (s : type686 A) (u : A -> Prop) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) v t) : (term182 A s t u v) = (True /\ True).
Proof. exact (MK_COMB (@lem4831481 A s v t h2) (@lem4831488 A u v h1)). Qed.
Lemma lem4831491 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4831492 : (True /\ True) = True.
Proof. exact (@lem4831491 True). Qed.
Lemma lem4831493 {A : Type'} (s : type686 A) (u : A -> Prop) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) v t) : (term182 A s t u v) = True.
Proof. exact (TRANS (@lem4831489 A s u v t h1 h2) (@lem4831492)). Qed.
Lemma lem4831494 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term184 A s t u v) = (True /\ True).
Proof. exact (MK_COMB (@lem4831467 A t u s h2) (@lem4831493 A s u v t h1 h3)). Qed.
Lemma lem4831496 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4831497 : (True /\ True) = True.
Proof. exact (@lem4831496 True). Qed.
Lemma lem4831498 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term184 A s t u v) = True.
Proof. exact (TRANS (@lem4831494 A u s v t h1 h2 h3) (@lem4831497)). Qed.
Lemma lem4831499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4831500 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term186 A s t u v) = (imp True).
Proof. exact (MK_COMB (@lem4831499) (@lem4831498 A u s v t h1 h2 h3)). Qed.
Lemma lem4831501 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@DISJOINT A u v) = (@DISJOINT A u v).
Proof. exact (eq_refl (@DISJOINT A u v)). Qed.
Lemma lem4831502 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term188 A s t u v) = (term393 A u v).
Proof. exact (MK_COMB (@lem4831500 A u s v t h1 h2 h3) (@lem4831501 A u v)). Qed.
Lemma lem4831504 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4831505 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term393 A u v) = (@DISJOINT A u v).
Proof. exact (@lem4831504 (@DISJOINT A u v)). Qed.
Lemma lem4831506 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term188 A s t u v) = (@DISJOINT A u v).
Proof. exact (TRANS (@lem4831502 A u s v t h1 h2 h3) (@lem4831505 A u v)). Qed.
Lemma lem4831507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4831508 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term388 A s t u v) = (term394 A u v).
Proof. exact (MK_COMB (@lem4831507) (@lem4831506 A u s v t h1 h2 h3)). Qed.
Lemma lem4831517 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (eq_refl (term237 A s t z)). Qed.
Lemma lem4831518 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term389 A u v s t z) = (term395 A u v s t z).
Proof. exact (MK_COMB (@lem4831508 A u s v t h1 h2 h3) (@lem4831517 A s t z)). Qed.
Lemma lem4831521 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : (term395 A u v s t z) = (term389 A u v s t z).
Proof. exact (SYM (@lem4831518 A z u s v t h1 h2 h3)). Qed.
Lemma lem4831523 (p : Prop) : p = (term295 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4831524 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term396 A s t z).
Proof. exact (@lem4831523 (term237 A s t z)). Qed.
Lemma lem4831525 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term396 A s t z) = (term237 A s t z).
Proof. exact (SYM (@lem4831524 A s t z)). Qed.
Lemma lem4831526 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term397 A s t z.
Proof. exact (h1). Qed.
Lemma lem4831529 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term398 A u v s t z) : term398 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4831530 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term399 A u v s t z.
Proof. exact (fun h0 : term398 A u v s t z => @lem4831529 A u v s t z h0). Qed.
Lemma lem4831531 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term399 A u v s t z) : term399 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4831532 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term398 A u v s t z) : term398 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4831533 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term399 A u v s t z) (h2 : term398 A u v s t z) : term398 A u v s t z.
Proof. exact (@lem4831531 A u v s t z h1 (@lem4831532 A u v s t z h2)). Qed.
Lemma lem4831534 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term398 A u v s t z) : term400 A u v s t z.
Proof. exact (fun h0 : term399 A u v s t z => @lem4831533 A u v s t z h0 h1). Qed.
Lemma lem4831535 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term399 A u v s t z) : term399 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4831536 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term399 A u v s t z) (h2 : term398 A u v s t z) : term398 A u v s t z.
Proof. exact (@lem4831534 A u v s t z h2 (@lem4831535 A u v s t z h1)). Qed.
Lemma lem4831537 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term399 A u v s t z) : term399 A u v s t z.
Proof. exact (fun h0 : term398 A u v s t z => @lem4831536 A u v s t z h1 h0). Qed.
Lemma lem4831538 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term401 A u v s t z.
Proof. exact (fun h0 : term399 A u v s t z => @lem4831537 A u v s t z h0). Qed.
Lemma lem4831541 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term399 A u v s t z.
Proof. exact (@lem4831538 A u v s t z (@lem4831530 A u v s t z)). Qed.
Lemma lem4831542 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term399 A u v s t z.
Proof. exact (@lem4831541 A u v s t z). Qed.
Lemma lem4831574 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4831575 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term396 A s t z) = (term402 A s t z).
Proof. exact (@lem4831574 (term397 A s t z)). Qed.
Lemma lem4831577 (t : Prop) : (term303 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4831578 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term402 A s t z) = (term237 A s t z).
Proof. exact (@lem4831577 (term237 A s t z)). Qed.
Lemma lem4831627 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term396 A s t z) = (term237 A s t z).
Proof. exact (TRANS (@lem4831575 A s t z) (@lem4831578 A s t z)). Qed.
Lemma lem4831632 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term403 A u v) = (term403 A u v).
Proof. exact (eq_refl (term403 A u v)). Qed.
Lemma lem4831633 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term404 A u v s t z) = (term405 A u v s t z).
Proof. exact (MK_COMB (@lem4831632 A u v) (@lem4831627 A s t z)). Qed.
Lemma lem4831636 {A : Type'} (z : A) (v : A -> Prop) : (term406 A z v) = (term406 A z v).
Proof. exact (eq_refl (term406 A z v)). Qed.
Lemma lem4831637 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term407 A u v s t z) = (term408 A u v s t z).
Proof. exact (MK_COMB (@lem4831636 A z v) (@lem4831633 A u v s t z)). Qed.
Lemma lem4831640 {A : Type'} (z : A) (u : A -> Prop) : (term406 A z u) = (term406 A z u).
Proof. exact (eq_refl (term406 A z u)). Qed.
Lemma lem4831641 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term409 A u v s t z) = (term410 A u v s t z).
Proof. exact (MK_COMB (@lem4831640 A z u) (@lem4831637 A u v s t z)). Qed.
Lemma lem4831644 {A : Type'} (v : A -> Prop) (t : type686 A) : (term411 A v t) = (term411 A v t).
Proof. exact (eq_refl (term411 A v t)). Qed.
Lemma lem4831645 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term412 A u v s t z) = (term413 A u v s t z).
Proof. exact (MK_COMB (@lem4831644 A v t) (@lem4831641 A u v s t z)). Qed.
Lemma lem4831648 {A : Type'} (u : A -> Prop) (s : type686 A) : (term411 A u s) = (term411 A u s).
Proof. exact (eq_refl (term411 A u s)). Qed.
Lemma lem4831649 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term398 A u v s t z) = (term414 A u v s t z).
Proof. exact (MK_COMB (@lem4831648 A u s) (@lem4831645 A u v s t z)). Qed.
Lemma lem4831652 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term415 A v s t z) = (term416 A v s t z).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4831649 A u v s t z)). Qed.
Lemma lem4831653 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831654 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term417 A v s t z) = (term418 A v s t z).
Proof. exact (MK_COMB (@lem4831653 A) (@lem4831652 A v s t z)). Qed.
Lemma lem4831659 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term419 A s t z) = (term420 A s t z).
Proof. exact (fun_ext (fun v : A -> Prop => @lem4831654 A v s t z)). Qed.
Lemma lem4831660 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831661 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term421 A s t z) = (term422 A s t z).
Proof. exact (MK_COMB (@lem4831660 A) (@lem4831659 A s t z)). Qed.
Lemma lem4831666 {A : Type'} (t : type686 A) (z : A) : (term423 A t z) = (term424 A t z).
Proof. exact (fun_ext (fun s : type686 A => @lem4831661 A s t z)). Qed.
Lemma lem4831667 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4831668 {A : Type'} (t : type686 A) (z : A) : (term425 A t z) = (term426 A t z).
Proof. exact (MK_COMB (@lem4831667 A) (@lem4831666 A t z)). Qed.
Lemma lem4831673 {A : Type'} (z : A) : (term427 A z) = (term428 A z).
Proof. exact (fun_ext (fun t : type686 A => @lem4831668 A t z)). Qed.
Lemma lem4831674 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4831675 {A : Type'} (z : A) : (term429 A z) = (term430 A z).
Proof. exact (MK_COMB (@lem4831674 A) (@lem4831673 A z)). Qed.
Lemma lem4831680 {A : Type'} : (term431 A) = (term432 A).
Proof. exact (fun_ext (fun z : A => @lem4831675 A z)). Qed.
Lemma lem4831681 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4831690 {A : Type'} : (term433 A) = (term434 A).
Proof. exact (MK_COMB (@lem4831681 A) (@lem4831680 A)). Qed.
Lemma lem4831699 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term234 A s t z t') = (term234 A s t z t').
Proof. exact (eq_refl (term234 A s t z t')). Qed.
Lemma lem4831700 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term236 A s t z) = (term236 A s t z).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4831699 A s t z t')). Qed.
Lemma lem4831701 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4831702 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (MK_COMB (@lem4831701 A) (@lem4831700 A s t z)). Qed.
Lemma lem4831705 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term403 A u v) = (term403 A u v).
Proof. exact (eq_refl (term403 A u v)). Qed.
Lemma lem4831706 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term405 A u v s t z) = (term405 A u v s t z).
Proof. exact (MK_COMB (@lem4831705 A u v) (@lem4831702 A s t z)). Qed.
Lemma lem4831709 {A : Type'} (z : A) (v : A -> Prop) : (term406 A z v) = (term406 A z v).
Proof. exact (eq_refl (term406 A z v)). Qed.
Lemma lem4831710 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term408 A u v s t z) = (term408 A u v s t z).
Proof. exact (MK_COMB (@lem4831709 A z v) (@lem4831706 A u v s t z)). Qed.
Lemma lem4831713 {A : Type'} (z : A) (u : A -> Prop) : (term406 A z u) = (term406 A z u).
Proof. exact (eq_refl (term406 A z u)). Qed.
Lemma lem4831714 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term410 A u v s t z) = (term410 A u v s t z).
Proof. exact (MK_COMB (@lem4831713 A z u) (@lem4831710 A u v s t z)). Qed.
Lemma lem4831717 {A : Type'} (v : A -> Prop) (t : type686 A) : (term411 A v t) = (term411 A v t).
Proof. exact (eq_refl (term411 A v t)). Qed.
Lemma lem4831718 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term413 A u v s t z) = (term413 A u v s t z).
Proof. exact (MK_COMB (@lem4831717 A v t) (@lem4831714 A u v s t z)). Qed.
Lemma lem4831721 {A : Type'} (u : A -> Prop) (s : type686 A) : (term411 A u s) = (term411 A u s).
Proof. exact (eq_refl (term411 A u s)). Qed.
Lemma lem4831722 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term414 A u v s t z) = (term414 A u v s t z).
Proof. exact (MK_COMB (@lem4831721 A u s) (@lem4831718 A u v s t z)). Qed.
Lemma lem4831723 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term416 A v s t z) = (term416 A v s t z).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4831722 A u v s t z)). Qed.
Lemma lem4831724 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831725 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term418 A v s t z) = (term418 A v s t z).
Proof. exact (MK_COMB (@lem4831724 A) (@lem4831723 A v s t z)). Qed.
Lemma lem4831726 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term420 A s t z) = (term420 A s t z).
Proof. exact (fun_ext (fun v : A -> Prop => @lem4831725 A v s t z)). Qed.
Lemma lem4831727 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831728 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term422 A s t z) = (term422 A s t z).
Proof. exact (MK_COMB (@lem4831727 A) (@lem4831726 A s t z)). Qed.
Lemma lem4831729 {A : Type'} (t : type686 A) (z : A) : (term424 A t z) = (term424 A t z).
Proof. exact (fun_ext (fun s : type686 A => @lem4831728 A s t z)). Qed.
Lemma lem4831730 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4831731 {A : Type'} (t : type686 A) (z : A) : (term426 A t z) = (term426 A t z).
Proof. exact (MK_COMB (@lem4831730 A) (@lem4831729 A t z)). Qed.
Lemma lem4831732 {A : Type'} (z : A) : (term428 A z) = (term428 A z).
Proof. exact (fun_ext (fun t : type686 A => @lem4831731 A t z)). Qed.
Lemma lem4831733 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4831734 {A : Type'} (z : A) : (term430 A z) = (term430 A z).
Proof. exact (MK_COMB (@lem4831733 A) (@lem4831732 A z)). Qed.
Lemma lem4831735 {A : Type'} : (term432 A) = (term432 A).
Proof. exact (fun_ext (fun z : A => @lem4831734 A z)). Qed.
Lemma lem4831736 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4831737 {A : Type'} : (term434 A) = (term434 A).
Proof. exact (MK_COMB (@lem4831736 A) (@lem4831735 A)). Qed.
Lemma lem4831790 {A : Type'} : (term433 A) = (term434 A).
Proof. exact (TRANS (@lem4831690 A) (@lem4831737 A)). Qed.
Lemma lem4831791 {A : Type'} : (term434 A) = (term433 A).
Proof. exact (SYM (@lem4831790 A)). Qed.
Lemma lem4831798 (p : Prop) : p = (term295 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4831799 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term396 A s t z).
Proof. exact (@lem4831798 (term237 A s t z)). Qed.
Lemma lem4831800 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term396 A s t z) = (term237 A s t z).
Proof. exact (SYM (@lem4831799 A s t z)). Qed.
Lemma lem4831801 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term397 A s t z.
Proof. exact (h1). Qed.
Lemma lem4831807 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : @IN (A -> Prop) u s.
Proof. exact (h1). Qed.
Lemma lem4831813 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : @IN (A -> Prop) v t.
Proof. exact (h1). Qed.
Lemma lem4831819 {A : Type'} (z : A) (u : A -> Prop) (h1 : @IN A z u) : @IN A z u.
Proof. exact (h1). Qed.
Lemma lem4831831 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : u = v.
Proof. exact (h1). Qed.
Lemma lem4831838 {A : Type'} (s : type686 A) (t : A -> Prop) (t' : type686 A) : (term435 A s t t') = (term436 A s t t').
Proof. exact (@lem17045 (@IN (A -> Prop) t s) (@IN (A -> Prop) t t')). Qed.
Lemma lem4831839 {A : Type'} (z : A) (t : A -> Prop) : (term369 A z t) = (term369 A z t).
Proof. exact (eq_refl (term369 A z t)). Qed.
Lemma lem4831840 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4831841 {A : Type'} (s : type686 A) (t : A -> Prop) (t' : type686 A) : (term437 A s t t') = (term438 A s t t').
Proof. exact (MK_COMB (@lem4831840) (@lem4831838 A s t t')). Qed.
Lemma lem4831842 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term439 A s t z t') = (term440 A s t z t').
Proof. exact (MK_COMB (@lem4831841 A s t' t) (@lem4831839 A z t')). Qed.
Lemma lem4831843 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term441 A s t z t') = (term439 A s t z t').
Proof. exact (@lem17045 (term230 A s t' t) (@IN A z t')). Qed.
Lemma lem4831844 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term441 A s t z t') = (term440 A s t z t').
Proof. exact (TRANS (@lem4831843 A s t z t') (@lem4831842 A s t z t')). Qed.
Lemma lem4831845 {A : Type'} (P : type686 A) : (term328 A P) = (term329 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4831846 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term397 A s t z) = (term442 A s t z).
Proof. exact (@lem4831845 A (term236 A s t z)). Qed.
Lemma lem4831847 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term443 A s t z t') = (term234 A s t z t').
Proof. exact (eq_refl (term443 A s t z t')). Qed.
Lemma lem4831848 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4831849 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term444 A s t z t') = (term441 A s t z t').
Proof. exact (MK_COMB (@lem4831848) (@lem4831847 A s t z t')). Qed.
Lemma lem4831850 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term444 A s t z t') = (term440 A s t z t').
Proof. exact (TRANS (@lem4831849 A s t z t') (@lem4831844 A s t z t')). Qed.
Lemma lem4831851 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term445 A s t z) = (term446 A s t z).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4831850 A s t z t')). Qed.
Lemma lem4831852 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831853 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term442 A s t z) = (term447 A s t z).
Proof. exact (MK_COMB (@lem4831852 A) (@lem4831851 A s t z)). Qed.
Lemma lem4831906 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term397 A s t z) = (term447 A s t z).
Proof. exact (TRANS (@lem4831846 A s t z) (@lem4831853 A s t z)). Qed.
Lemma lem4831907 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term447 A s t z.
Proof. exact (EQ_MP (@lem4831906 A s t z) (@lem4831801 A s t z h1)). Qed.
Lemma lem4831913 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : @IN (A -> Prop) u s.
Proof. exact (h1). Qed.
Lemma lem4831919 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : @IN (A -> Prop) v t.
Proof. exact (h1). Qed.
Lemma lem4831925 {A : Type'} (z : A) (u : A -> Prop) (h1 : @IN A z u) : @IN A z u.
Proof. exact (h1). Qed.
Lemma lem4831937 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : u = v.
Proof. exact (h1). Qed.
Lemma lem4831964 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term440 A s t z t') = (term440 A s t z t').
Proof. exact (eq_refl (term440 A s t z t')). Qed.
Lemma lem4831965 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term446 A s t z) = (term446 A s t z).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4831964 A s t z t')). Qed.
Lemma lem4831966 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4831967 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term447 A s t z) = (term447 A s t z).
Proof. exact (MK_COMB (@lem4831966 A) (@lem4831965 A s t z)). Qed.
Lemma lem4831968 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term447 A s t z.
Proof. exact (EQ_MP (@lem4831967 A s t z) (@lem4831907 A s t z h1)). Qed.
Lemma lem4831972 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : @IN (A -> Prop) u s.
Proof. exact (h1). Qed.
Lemma lem4831976 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : @IN (A -> Prop) v t.
Proof. exact (h1). Qed.
Lemma lem4831980 {A : Type'} (z : A) (u : A -> Prop) (h1 : @IN A z u) : @IN A z u.
Proof. exact (h1). Qed.
Lemma lem4831988 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : u = v.
Proof. exact (h1). Qed.
Lemma lem4832002 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (t' : A -> Prop) : (term440 A s t z t') = (term440 A s t z t').
Proof. exact (eq_refl (term440 A s t z t')). Qed.
Lemma lem4832003 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term446 A s t z) = (term446 A s t z).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4832002 A s t z t')). Qed.
Lemma lem4832004 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4832006 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term447 A s t z) = (term447 A s t z).
Proof. exact (MK_COMB (@lem4832004 A) (@lem4832003 A s t z)). Qed.
Lemma lem4832007 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term447 A s t z.
Proof. exact (EQ_MP (@lem4832006 A s t z) (@lem4831968 A s t z h1)). Qed.
Lemma lem4832008 {A : Type'} (_59842 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term448 A s t z _59842.
Proof. exact (@lem4832007 A s t z h1 _59842). Qed.
Lemma lem4832009 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (_59842 : A -> Prop) : (term448 A s t z _59842) = (term440 A s t z _59842).
Proof. exact (eq_refl (term448 A s t z _59842)). Qed.
Lemma lem4832010 {A : Type'} (_59842 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term440 A s t z _59842.
Proof. exact (EQ_MP (@lem4832009 A s t z _59842) (@lem4832008 A _59842 s t z h1)). Qed.
Lemma lem4832012 {A : Type'} (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : @IN (A -> Prop) u s.
Proof. exact (h1). Qed.
Lemma lem4832014 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : @IN (A -> Prop) v t.
Proof. exact (h1). Qed.
Lemma lem4832016 {A : Type'} (z : A) (u : A -> Prop) (h1 : @IN A z u) : @IN A z u.
Proof. exact (h1). Qed.
Lemma lem4832020 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : u = v.
Proof. exact (h1). Qed.
Lemma lem4832031 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (_59842 : A -> Prop) : (term440 A s t z _59842) = (term449 A s t z _59842).
Proof. exact (@lem4829802 (term351 A _59842 s) (term351 A _59842 t) (term369 A z _59842)). Qed.
Lemma lem4832047 {A : Type'} (s : type686 A) : (term450 A s) = (term450 A s).
Proof. exact (eq_refl (term450 A s)). Qed.
Lemma lem4832048 {A : Type'} (s : type686 A) (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (term451 A s u) = (term451 A s v).
Proof. exact (MK_COMB (@lem4832047 A s) (@lem4832020 A u v h1)). Qed.
Lemma lem4832049 {A : Type'} (v : A -> Prop) (s : type686 A) : (term451 A s v) = (@IN (A -> Prop) v s).
Proof. exact (eq_refl (term451 A s v)). Qed.
Lemma lem4832050 {A : Type'} (s : type686 A) (u : A -> Prop) : (term452 A s u) = (term452 A s u).
Proof. exact (eq_refl (term452 A s u)). Qed.
Lemma lem4832051 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) : ((term451 A s u) = (term451 A s v)) = ((term451 A s u) = (@IN (A -> Prop) v s)).
Proof. exact (MK_COMB (@lem4832050 A s u) (@lem4832049 A v s)). Qed.
Lemma lem4832052 {A : Type'} (u : A -> Prop) (s : type686 A) : (term451 A s u) = (@IN (A -> Prop) u s).
Proof. exact (eq_refl (term451 A s u)). Qed.
Lemma lem4832053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4832054 {A : Type'} (u : A -> Prop) (s : type686 A) : (term452 A s u) = (term453 A u s).
Proof. exact (MK_COMB (@lem4832053) (@lem4832052 A u s)). Qed.
Lemma lem4832055 {A : Type'} (v : A -> Prop) (s : type686 A) : (@IN (A -> Prop) v s) = (@IN (A -> Prop) v s).
Proof. exact (eq_refl (@IN (A -> Prop) v s)). Qed.
Lemma lem4832056 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) : ((term451 A s u) = (@IN (A -> Prop) v s)) = ((@IN (A -> Prop) u s) = (@IN (A -> Prop) v s)).
Proof. exact (MK_COMB (@lem4832054 A u s) (@lem4832055 A v s)). Qed.
Lemma lem4832057 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) : ((term451 A s u) = (term451 A s v)) = ((@IN (A -> Prop) u s) = (@IN (A -> Prop) v s)).
Proof. exact (TRANS (@lem4832051 A u v s) (@lem4832056 A u v s)). Qed.
Lemma lem4832058 {A : Type'} (s : type686 A) (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (@IN (A -> Prop) u s) = (@IN (A -> Prop) v s).
Proof. exact (EQ_MP (@lem4832057 A u v s) (@lem4832048 A s u v h1)). Qed.
Lemma lem4832073 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : @IN (A -> Prop) v t.
Proof. exact (h1). Qed.
Lemma lem4832074 {A : Type'} (z : A) : (term454 A z) = (term454 A z).
Proof. exact (eq_refl (term454 A z)). Qed.
Lemma lem4832075 {A : Type'} (z : A) (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (term455 A z u) = (term455 A z v).
Proof. exact (MK_COMB (@lem4832074 A z) (@lem4832020 A u v h1)). Qed.
Lemma lem4832076 {A : Type'} (z : A) (v : A -> Prop) : (term455 A z v) = (@IN A z v).
Proof. exact (eq_refl (term455 A z v)). Qed.
Lemma lem4832077 {A : Type'} (z : A) (u : A -> Prop) : (term456 A z u) = (term456 A z u).
Proof. exact (eq_refl (term456 A z u)). Qed.
Lemma lem4832078 {A : Type'} (u : A -> Prop) (z : A) (v : A -> Prop) : ((term455 A z u) = (term455 A z v)) = ((term455 A z u) = (@IN A z v)).
Proof. exact (MK_COMB (@lem4832077 A z u) (@lem4832076 A z v)). Qed.
Lemma lem4832079 {A : Type'} (z : A) (u : A -> Prop) : (term455 A z u) = (@IN A z u).
Proof. exact (eq_refl (term455 A z u)). Qed.
Lemma lem4832080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4832081 {A : Type'} (z : A) (u : A -> Prop) : (term456 A z u) = (term457 A z u).
Proof. exact (MK_COMB (@lem4832080) (@lem4832079 A z u)). Qed.
Lemma lem4832082 {A : Type'} (z : A) (v : A -> Prop) : (@IN A z v) = (@IN A z v).
Proof. exact (eq_refl (@IN A z v)). Qed.
Lemma lem4832083 {A : Type'} (u : A -> Prop) (z : A) (v : A -> Prop) : ((term455 A z u) = (@IN A z v)) = ((@IN A z u) = (@IN A z v)).
Proof. exact (MK_COMB (@lem4832081 A z u) (@lem4832082 A z v)). Qed.
Lemma lem4832084 {A : Type'} (u : A -> Prop) (z : A) (v : A -> Prop) : ((term455 A z u) = (term455 A z v)) = ((@IN A z u) = (@IN A z v)).
Proof. exact (TRANS (@lem4832078 A u z v) (@lem4832083 A u z v)). Qed.
Lemma lem4832085 {A : Type'} (z : A) (u : A -> Prop) (v : A -> Prop) (h1 : u = v) : (@IN A z u) = (@IN A z v).
Proof. exact (EQ_MP (@lem4832084 A u z v) (@lem4832075 A z u v h1)). Qed.
Lemma lem4832086 {A : Type'} (v : A -> Prop) (z : A) (u : A -> Prop) (h1 : u = v) (h2 : @IN A z u) : @IN A z v.
Proof. exact (EQ_MP (@lem4832085 A z u v h1) (@lem4832016 A z u h2)). Qed.
Lemma lem4832100 {A : Type'} (z : A) (v : A -> Prop) (h1 : @IN A z v) : @IN A z v.
Proof. exact (h1). Qed.
Lemma lem4832114 {A : Type'} (_59842 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term449 A s t z _59842.
Proof. exact (EQ_MP (@lem4832031 A s t z _59842) (@lem4832010 A _59842 s t z h1)). Qed.
Lemma lem4832116 {A : Type'} (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) : @IN (A -> Prop) v s.
Proof. exact (EQ_MP (@lem4832058 A s u v h1) (@lem4832012 A u s h2)). Qed.
Lemma lem4832117 {A : Type'} (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) : term366 A v s.
Proof. exact (fun h0 : term351 A v s => @lem4832116 A v u s h1 h2). Qed.
Lemma lem4832119 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4832120 {A : Type'} (v : A -> Prop) (s : type686 A) : (term366 A v s) = (@IN (A -> Prop) v s).
Proof. exact (@lem4832119 (@IN (A -> Prop) v s)). Qed.
Lemma lem4832121 {A : Type'} (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : u = v) (h2 : @IN (A -> Prop) u s) : @IN (A -> Prop) v s.
Proof. exact (EQ_MP (@lem4832120 A v s) (@lem4832117 A v u s h1 h2)). Qed.
Lemma lem4832123 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : @IN (A -> Prop) v t.
Proof. exact (h1). Qed.
Lemma lem4832124 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : term366 A v t.
Proof. exact (fun h0 : term351 A v t => @lem4832123 A v t h1). Qed.
Lemma lem4832126 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4832127 {A : Type'} (v : A -> Prop) (t : type686 A) : (term366 A v t) = (@IN (A -> Prop) v t).
Proof. exact (@lem4832126 (@IN (A -> Prop) v t)). Qed.
Lemma lem4832128 {A : Type'} (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) v t) : @IN (A -> Prop) v t.
Proof. exact (EQ_MP (@lem4832127 A v t) (@lem4832124 A v t h1)). Qed.
Lemma lem4832130 {A : Type'} (z : A) (v : A -> Prop) (h1 : @IN A z v) : @IN A z v.
Proof. exact (h1). Qed.
Lemma lem4832131 {A : Type'} (z : A) (v : A -> Prop) (h1 : @IN A z v) : term368 A z v.
Proof. exact (fun h0 : term369 A z v => @lem4832130 A z v h1). Qed.
Lemma lem4832133 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4832134 {A : Type'} (z : A) (v : A -> Prop) : (term368 A z v) = (@IN A z v).
Proof. exact (@lem4832133 (@IN A z v)). Qed.
Lemma lem4832135 {A : Type'} (z : A) (v : A -> Prop) (h1 : @IN A z v) : @IN A z v.
Proof. exact (EQ_MP (@lem4832134 A z v) (@lem4832131 A z v h1)). Qed.
Lemma lem4832137 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4832138 {A : Type'} (t : type686 A) (z : A) (_59842 : A -> Prop) : (term458 A t z _59842) = (term459 A t z _59842).
Proof. exact (@lem4832137 (@IN (A -> Prop) _59842 t) (@IN A z _59842)). Qed.
Lemma lem4832139 {A : Type'} (_59842 : A -> Prop) (s : type686 A) : (term324 A _59842 s) = (term324 A _59842 s).
Proof. exact (eq_refl (term324 A _59842 s)). Qed.
Lemma lem4832140 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (_59842 : A -> Prop) : (term449 A s t z _59842) = (term460 A s t z _59842).
Proof. exact (MK_COMB (@lem4832139 A _59842 s) (@lem4832138 A t z _59842)). Qed.
Lemma lem4832142 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4832143 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (_59842 : A -> Prop) : (term460 A s t z _59842) = (term461 A s t z _59842).
Proof. exact (@lem4832142 (@IN (A -> Prop) _59842 s) (term462 A t z _59842)). Qed.
Lemma lem4832144 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (_59842 : A -> Prop) : (term449 A s t z _59842) = (term461 A s t z _59842).
Proof. exact (TRANS (@lem4832140 A s t z _59842) (@lem4832143 A s t z _59842)). Qed.
Lemma lem4832146 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4832147 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (_59842 : A -> Prop) : (term461 A s t z _59842) = (term463 A s t z _59842).
Proof. exact (@lem4832146 (term464 A s t z _59842)). Qed.
Lemma lem4832148 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (_59842 : A -> Prop) : (term449 A s t z _59842) = (term463 A s t z _59842).
Proof. exact (TRANS (@lem4832144 A s t z _59842) (@lem4832147 A s t z _59842)). Qed.
Lemma lem4832150 {A : Type'} (z : A) (v : A -> Prop) (t : type686 A) (h1 : @IN A z v) (h2 : @IN (A -> Prop) v t) : term462 A t z v.
Proof. exact (conj (@lem4832128 A v t h2) (@lem4832135 A z v h1)). Qed.
Lemma lem4832151 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN A z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term464 A s t z v.
Proof. exact (conj (@lem4832121 A v u s h1 h3) (@lem4832150 A z v t h2 h4)). Qed.
Lemma lem4832153 {A : Type'} (_59842 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term463 A s t z _59842.
Proof. exact (EQ_MP (@lem4832148 A s t z _59842) (@lem4832114 A _59842 s t z h1)). Qed.
Lemma lem4832154 {A : Type'} (_59842 : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term463 A s t z _59842.
Proof. exact (@lem4832153 A _59842 s t z h1). Qed.
Lemma lem4832155 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term397 A s t z) : term463 A s t z v.
Proof. exact (@lem4832154 A v s t z h1). Qed.
Lemma lem4832158 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (@lem4832155 A v s t z h1 (@lem4832151 A z u s v t h2 h3 h4 h5)). Qed.
Lemma lem4832159 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term379.
Proof. exact (fun h0 : ~ False => @lem4832158 A z u s v t h1 h2 h3 h4 h5). Qed.
Lemma lem4832161 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4832162 : term379 = False.
Proof. exact (@lem4832161 False). Qed.
Lemma lem4832163 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832162) (@lem4832159 A z u s v t h1 h2 h3 h4 h5)). Qed.
Lemma lem4832164 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z v) = False.
Proof. exact (prop_ext (fun h6 : @IN A z v => @lem4832163 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4832100 A z v h3)). Qed.
Lemma lem4832165 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832164 A z u s v t h1 h2 h3 h4 h5) (@lem4832100 A z v h3)). Qed.
Lemma lem4832166 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z v) = False.
Proof. exact (prop_ext (fun h6 : @IN A z v => @lem4832165 A z u s v t h1 h2 h6 h4 h5) (fun h6 : False => @lem4832086 A v z u h2 h3)). Qed.
Lemma lem4832167 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832166 A z u s v t h1 h2 h3 h4 h5) (@lem4832086 A v z u h2 h3)). Qed.
Lemma lem4832168 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) v t => @lem4832167 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4832073 A v t h5)). Qed.
Lemma lem4832170 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832168 A z u s v t h1 h2 h3 h4 h5) (@lem4832073 A v t h5)). Qed.
Lemma lem4832171 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (u = v) = False.
Proof. exact (prop_ext (fun h6 : u = v => @lem4832170 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4832020 A u v h2)). Qed.
Lemma lem4832172 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832171 A z u s v t h1 h2 h3 h4 h5) (@lem4832020 A u v h2)). Qed.
Lemma lem4832173 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z u) = False.
Proof. exact (prop_ext (fun h6 : @IN A z u => @lem4832172 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4832016 A z u h3)). Qed.
Lemma lem4832174 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832173 A z u s v t h1 h2 h3 h4 h5) (@lem4832016 A z u h3)). Qed.
Lemma lem4832175 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) v t => @lem4832174 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4832014 A v t h5)). Qed.
Lemma lem4832176 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832175 A z u s v t h1 h2 h3 h4 h5) (@lem4832014 A v t h5)). Qed.
Lemma lem4832177 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) u s) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) u s => @lem4832176 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4832012 A u s h4)). Qed.
Lemma lem4832178 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832177 A z u s v t h1 h2 h3 h4 h5) (@lem4832012 A u s h4)). Qed.
Lemma lem4832179 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (u = v) = False.
Proof. exact (prop_ext (fun h6 : u = v => @lem4832178 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831988 A u v h2)). Qed.
Lemma lem4832180 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832179 A z u s v t h1 h2 h3 h4 h5) (@lem4831988 A u v h2)). Qed.
Lemma lem4832181 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z u) = False.
Proof. exact (prop_ext (fun h6 : @IN A z u => @lem4832180 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831980 A z u h3)). Qed.
Lemma lem4832182 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832181 A z u s v t h1 h2 h3 h4 h5) (@lem4831980 A z u h3)). Qed.
Lemma lem4832183 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) v t => @lem4832182 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831976 A v t h5)). Qed.
Lemma lem4832184 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832183 A z u s v t h1 h2 h3 h4 h5) (@lem4831976 A v t h5)). Qed.
Lemma lem4832185 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) u s) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) u s => @lem4832184 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831972 A u s h4)). Qed.
Lemma lem4832186 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832185 A z u s v t h1 h2 h3 h4 h5) (@lem4831972 A u s h4)). Qed.
Lemma lem4832187 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (u = v) = False.
Proof. exact (prop_ext (fun h6 : u = v => @lem4832186 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831988 A u v h2)). Qed.
Lemma lem4832188 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832187 A z u s v t h1 h2 h3 h4 h5) (@lem4831988 A u v h2)). Qed.
Lemma lem4832189 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z u) = False.
Proof. exact (prop_ext (fun h6 : @IN A z u => @lem4832188 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831980 A z u h3)). Qed.
Lemma lem4832190 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832189 A z u s v t h1 h2 h3 h4 h5) (@lem4831980 A z u h3)). Qed.
Lemma lem4832191 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) v t => @lem4832190 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831976 A v t h5)). Qed.
Lemma lem4832192 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832191 A z u s v t h1 h2 h3 h4 h5) (@lem4831976 A v t h5)). Qed.
Lemma lem4832193 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) u s) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) u s => @lem4832192 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831972 A u s h4)). Qed.
Lemma lem4832194 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832193 A z u s v t h1 h2 h3 h4 h5) (@lem4831972 A u s h4)). Qed.
Lemma lem4832195 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (u = v) = False.
Proof. exact (prop_ext (fun h6 : u = v => @lem4832194 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831937 A u v h2)). Qed.
Lemma lem4832196 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832195 A z u s v t h1 h2 h3 h4 h5) (@lem4831937 A u v h2)). Qed.
Lemma lem4832197 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z u) = False.
Proof. exact (prop_ext (fun h6 : @IN A z u => @lem4832196 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831925 A z u h3)). Qed.
Lemma lem4832198 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832197 A z u s v t h1 h2 h3 h4 h5) (@lem4831925 A z u h3)). Qed.
Lemma lem4832199 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) v t => @lem4832198 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831919 A v t h5)). Qed.
Lemma lem4832200 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832199 A z u s v t h1 h2 h3 h4 h5) (@lem4831919 A v t h5)). Qed.
Lemma lem4832201 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) u s) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) u s => @lem4832200 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831913 A u s h4)). Qed.
Lemma lem4832202 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832201 A z u s v t h1 h2 h3 h4 h5) (@lem4831913 A u s h4)). Qed.
Lemma lem4832203 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (u = v) = False.
Proof. exact (prop_ext (fun h6 : u = v => @lem4832202 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831831 A u v h2)). Qed.
Lemma lem4832204 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832203 A z u s v t h1 h2 h3 h4 h5) (@lem4831831 A u v h2)). Qed.
Lemma lem4832205 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z u) = False.
Proof. exact (prop_ext (fun h6 : @IN A z u => @lem4832204 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831819 A z u h3)). Qed.
Lemma lem4832206 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832205 A z u s v t h1 h2 h3 h4 h5) (@lem4831819 A z u h3)). Qed.
Lemma lem4832207 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) v t => @lem4832206 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831813 A v t h5)). Qed.
Lemma lem4832208 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832207 A z u s v t h1 h2 h3 h4 h5) (@lem4831813 A v t h5)). Qed.
Lemma lem4832209 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN (A -> Prop) u s) = False.
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) u s => @lem4832208 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831807 A u s h4)). Qed.
Lemma lem4832210 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832209 A z u s v t h1 h2 h3 h4 h5) (@lem4831807 A u s h4)). Qed.
Lemma lem4832211 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (term397 A s t z) = False.
Proof. exact (prop_ext (fun h6 : term397 A s t z => @lem4832210 A z u s v t h1 h2 h3 h4 h5) (fun h6 : False => @lem4831801 A s t z h1)). Qed.
Lemma lem4832212 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832211 A z u s v t h1 h2 h3 h4 h5) (@lem4831801 A s t z h1)). Qed.
Lemma lem4832213 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN A z u) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term396 A s t z.
Proof. exact (fun h0 : term397 A s t z => @lem4832212 A z u s v t h0 h1 h2 h3 h4). Qed.
Lemma lem4832214 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN A z u) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (EQ_MP (@lem4831800 A s t z) (@lem4832213 A z u s v t h1 h2 h3 h4)). Qed.
Lemma lem4832215 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN A z u) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : term405 A u v s t z.
Proof. exact (fun h0 : u = v => @lem4832214 A z u s v t h0 h1 h2 h3). Qed.
Lemma lem4832216 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN A z u) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : term408 A u v s t z.
Proof. exact (fun h0 : @IN A z v => @lem4832215 A z u s v t h1 h2 h3). Qed.
Lemma lem4832217 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) u s) (h2 : @IN (A -> Prop) v t) : term410 A u v s t z.
Proof. exact (fun h0 : @IN A z u => @lem4832216 A z u s v t h0 h1 h2). Qed.
Lemma lem4832218 {A : Type'} (v : A -> Prop) (t : type686 A) (z : A) (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : term413 A u v s t z.
Proof. exact (fun h0 : @IN (A -> Prop) v t => @lem4832217 A z u s v t h1 h0). Qed.
Lemma lem4832219 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term414 A u v s t z.
Proof. exact (fun h0 : @IN (A -> Prop) u s => @lem4832218 A v t z u s h0). Qed.
Lemma lem4832224 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term418 A v s t z.
Proof. exact (fun u : A -> Prop => @lem4832219 A u v s t z). Qed.
Lemma lem4832229 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term422 A s t z.
Proof. exact (fun v : A -> Prop => @lem4832224 A v s t z). Qed.
Lemma lem4832234 {A : Type'} (t : type686 A) (z : A) : term426 A t z.
Proof. exact (fun s : type686 A => @lem4832229 A s t z). Qed.
Lemma lem4832239 {A : Type'} (z : A) : term430 A z.
Proof. exact (fun t : type686 A => @lem4832234 A t z). Qed.
Lemma lem4832244 {A : Type'} : term434 A.
Proof. exact (fun z : A => @lem4832239 A z). Qed.
Lemma lem4832245 {A : Type'} : term433 A.
Proof. exact (EQ_MP (@lem4831791 A) (@lem4832244 A)). Qed.
Lemma lem4832246 {A : Type'} (z : A) : term465 A z.
Proof. exact (@lem4832245 A z). Qed.
Lemma lem4832247 {A : Type'} (z : A) : (term465 A z) = (term429 A z).
Proof. exact (eq_refl (term465 A z)). Qed.
Lemma lem4832248 {A : Type'} (z : A) : term429 A z.
Proof. exact (EQ_MP (@lem4832247 A z) (@lem4832246 A z)). Qed.
Lemma lem4832249 {A : Type'} (z : A) (t : type686 A) : term466 A z t.
Proof. exact (@lem4832248 A z t). Qed.
Lemma lem4832250 {A : Type'} (t : type686 A) (z : A) : (term466 A z t) = (term425 A t z).
Proof. exact (eq_refl (term466 A z t)). Qed.
Lemma lem4832251 {A : Type'} (t : type686 A) (z : A) : term425 A t z.
Proof. exact (EQ_MP (@lem4832250 A t z) (@lem4832249 A z t)). Qed.
Lemma lem4832252 {A : Type'} (t : type686 A) (z : A) (s : type686 A) : term467 A t z s.
Proof. exact (@lem4832251 A t z s). Qed.
Lemma lem4832253 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term467 A t z s) = (term421 A s t z).
Proof. exact (eq_refl (term467 A t z s)). Qed.
Lemma lem4832254 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term421 A s t z.
Proof. exact (EQ_MP (@lem4832253 A s t z) (@lem4832252 A t z s)). Qed.
Lemma lem4832255 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (v : A -> Prop) : term468 A s t z v.
Proof. exact (@lem4832254 A s t z v). Qed.
Lemma lem4832256 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term468 A s t z v) = (term417 A v s t z).
Proof. exact (eq_refl (term468 A s t z v)). Qed.
Lemma lem4832257 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term417 A v s t z.
Proof. exact (EQ_MP (@lem4832256 A v s t z) (@lem4832255 A s t z v)). Qed.
Lemma lem4832258 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (u : A -> Prop) : term469 A v s t z u.
Proof. exact (@lem4832257 A v s t z u). Qed.
Lemma lem4832259 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term469 A v s t z u) = (term398 A u v s t z).
Proof. exact (eq_refl (term469 A v s t z u)). Qed.
Lemma lem4832260 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term398 A u v s t z.
Proof. exact (EQ_MP (@lem4832259 A u v s t z) (@lem4832258 A v s t z u)). Qed.
Lemma lem4832262 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term398 A u v s t z.
Proof. exact (@lem4831542 A u v s t z (@lem4832260 A u v s t z)). Qed.
Lemma lem4832263 {A : Type'} (v : A -> Prop) (t : type686 A) (z : A) (u : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) u s) : term412 A u v s t z.
Proof. exact (@lem4832262 A u v s t z (@lem4831300 A u s h1)). Qed.
Lemma lem4832264 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) u s) (h2 : @IN (A -> Prop) v t) : term409 A u v s t z.
Proof. exact (@lem4832263 A v t z u s h1 (@lem4831302 A v t h2)). Qed.
Lemma lem4832265 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN A z u) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : term407 A u v s t z.
Proof. exact (@lem4832264 A z u s v t h2 h3 (@lem4831304 A z u h1)). Qed.
Lemma lem4832266 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN A z u) (h2 : @IN A z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term404 A u v s t z.
Proof. exact (@lem4832265 A z u s v t h1 h3 h4 (@lem4831303 A z v h2)). Qed.
Lemma lem4832267 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term396 A s t z.
Proof. exact (@lem4832266 A z u s v t h2 h3 h4 h5 (@lem4829806 A u v h1)). Qed.
Lemma lem4832268 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN A z v) (h5 : @IN (A -> Prop) u s) (h6 : @IN (A -> Prop) v t) : False.
Proof. exact (@lem4832267 A z u s v t h2 h3 h4 h5 h6 (@lem4831526 A s t z h1)). Qed.
Lemma lem4832269 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN A z v) (h5 : @IN (A -> Prop) u s) (h6 : @IN (A -> Prop) v t) : (term397 A s t z) = False.
Proof. exact (prop_ext (fun h7 : term397 A s t z => @lem4832268 A z u s v t h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem4831526 A s t z h1)). Qed.
Lemma lem4832270 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term397 A s t z) (h2 : u = v) (h3 : @IN A z u) (h4 : @IN A z v) (h5 : @IN (A -> Prop) u s) (h6 : @IN (A -> Prop) v t) : False.
Proof. exact (EQ_MP (@lem4832269 A z u s v t h1 h2 h3 h4 h5 h6) (@lem4831526 A s t z h1)). Qed.
Lemma lem4832271 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term396 A s t z.
Proof. exact (fun h0 : term397 A s t z => @lem4832270 A z u s v t h0 h1 h2 h3 h4 h5). Qed.
Lemma lem4832272 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (EQ_MP (@lem4831525 A s t z) (@lem4832271 A z u s v t h1 h2 h3 h4 h5)). Qed.
Lemma lem4832283 {A : Type'} (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) u s) (h2 : @IN (A -> Prop) v t) : term470 A v t u s.
Proof. exact (conj (@lem4831302 A v t h2) (@lem4831300 A u s h1)). Qed.
Lemma lem4832284 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN A z u) (h2 : @IN (A -> Prop) u s) (h3 : @IN (A -> Prop) v t) : term471 A z v t u s.
Proof. exact (conj (@lem4831304 A z u h1) (@lem4832283 A u s v t h2 h3)). Qed.
Lemma lem4832285 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN A z u) (h2 : @IN A z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term472 A z v t u s.
Proof. exact (conj (@lem4831303 A z v h2) (@lem4832284 A z u s v t h1 h3 h4)). Qed.
Lemma lem4832286 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term473 A z v t u s.
Proof. exact (conj (@lem4829807 A u v h1) (@lem4832285 A z u s v t h2 h3 h4 h5)). Qed.
Lemma lem4832294 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term51 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4832295 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term51 A s t).
Proof. exact (@lem4832294 A s t). Qed.
Lemma lem4832296 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (u = v) = (term51 A u v).
Proof. exact (@lem4832295 A u v). Qed.
Lemma lem4832305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4832306 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term9 A u v) = (term474 A u v).
Proof. exact (MK_COMB (@lem4832305) (@lem4832296 A u v)). Qed.
Lemma lem4832307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832308 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term475 A u v) = (term476 A u v).
Proof. exact (MK_COMB (@lem4832307) (@lem4832306 A u v)). Qed.
Lemma lem4832315 {A : Type'} (z : A) (v : A -> Prop) (t : type686 A) (u : A -> Prop) (s : type686 A) : (term472 A z v t u s) = (term472 A z v t u s).
Proof. exact (eq_refl (term472 A z v t u s)). Qed.
Lemma lem4832316 {A : Type'} (z : A) (v : A -> Prop) (t : type686 A) (u : A -> Prop) (s : type686 A) : (term473 A z v t u s) = (term477 A z v t u s).
Proof. exact (MK_COMB (@lem4832308 A u v) (@lem4832315 A z v t u s)). Qed.
Lemma lem4832319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4832320 {A : Type'} (z : A) (v : A -> Prop) (t : type686 A) (u : A -> Prop) (s : type686 A) : (term478 A z v t u s) = (term479 A z v t u s).
Proof. exact (MK_COMB (@lem4832319) (@lem4832316 A z v t u s)). Qed.
Lemma lem4832324 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem4832325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem4832324 A s t). Qed.
Lemma lem4832326 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@DISJOINT A u v) = ((@INTER A u v) = (@EMPTY A)).
Proof. exact (@lem4832325 A u v). Qed.
Lemma lem4832330 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term51 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4832331 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term51 A s t).
Proof. exact (@lem4832330 A s t). Qed.
Lemma lem4832332 {A : Type'} (u : A -> Prop) (v : A -> Prop) : ((@INTER A u v) = (@EMPTY A)) = (term480 A u v).
Proof. exact (@lem4832331 A (@INTER A u v) (@EMPTY A)). Qed.
Lemma lem4832337 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@DISJOINT A u v) = (term480 A u v).
Proof. exact (TRANS (@lem4832326 A u v) (@lem4832332 A u v)). Qed.
Lemma lem4832342 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4832343 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term394 A u v) = (term481 A u v).
Proof. exact (MK_COMB (@lem4832342) (@lem4832337 A u v)). Qed.
Lemma lem4832352 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term237 A s t z).
Proof. exact (eq_refl (term237 A s t z)). Qed.
Lemma lem4832353 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term395 A u v s t z) = (term482 A u v s t z).
Proof. exact (MK_COMB (@lem4832343 A u v) (@lem4832352 A s t z)). Qed.
Lemma lem4832356 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term483 A u v s t z) = (term484 A u v s t z).
Proof. exact (MK_COMB (@lem4832320 A z v t u s) (@lem4832353 A u v s t z)). Qed.
Lemma lem4832359 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term484 A u v s t z) = (term483 A u v s t z).
Proof. exact (SYM (@lem4832356 A u v s t z)). Qed.
Lemma lem4832371 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832372 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4832371 A P x). Qed.
Lemma lem4832373 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem4832372 A u x). Qed.
Lemma lem4832374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4832375 {A : Type'} (u : A -> Prop) (x : A) : (term457 A x u) = (term485 A u x).
Proof. exact (MK_COMB (@lem4832374) (@lem4832373 A u x)). Qed.
Lemma lem4832377 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832378 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4832377 A P x). Qed.
Lemma lem4832379 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem4832378 A v x). Qed.
Lemma lem4832380 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((@IN A x u) = (@IN A x v)) = ((u x) = (v x)).
Proof. exact (MK_COMB (@lem4832375 A u x) (@lem4832379 A v x)). Qed.
Lemma lem4832383 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term486 A u v) = (term487 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832380 A u v x)). Qed.
Lemma lem4832384 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4832385 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term51 A u v) = (term488 A u v).
Proof. exact (MK_COMB (@lem4832384 A) (@lem4832383 A u v)). Qed.
Lemma lem4832390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4832391 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term474 A u v) = (term489 A u v).
Proof. exact (MK_COMB (@lem4832390) (@lem4832385 A u v)). Qed.
Lemma lem4832392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832393 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term476 A u v) = (term490 A u v).
Proof. exact (MK_COMB (@lem4832392) (@lem4832391 A u v)). Qed.
Lemma lem4832397 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832398 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4832397 A P x). Qed.
Lemma lem4832399 {A : Type'} (v : A -> Prop) (z : A) : (@IN A z v) = (v z).
Proof. exact (@lem4832398 A v z). Qed.
Lemma lem4832400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832401 {A : Type'} (v : A -> Prop) (z : A) : (term491 A z v) = (term492 A v z).
Proof. exact (MK_COMB (@lem4832400) (@lem4832399 A v z)). Qed.
Lemma lem4832405 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832406 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4832405 A P x). Qed.
Lemma lem4832407 {A : Type'} (u : A -> Prop) (z : A) : (@IN A z u) = (u z).
Proof. exact (@lem4832406 A u z). Qed.
Lemma lem4832408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832409 {A : Type'} (u : A -> Prop) (z : A) : (term491 A z u) = (term492 A u z).
Proof. exact (MK_COMB (@lem4832408) (@lem4832407 A u z)). Qed.
Lemma lem4832413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832414 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4832413 (A -> Prop) P x). Qed.
Lemma lem4832415 {A : Type'} (t : type686 A) (v : A -> Prop) : (@IN (A -> Prop) v t) = (t v).
Proof. exact (@lem4832414 A t v). Qed.
Lemma lem4832416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832417 {A : Type'} (t : type686 A) (v : A -> Prop) : (term118 A v t) = (term493 A t v).
Proof. exact (MK_COMB (@lem4832416) (@lem4832415 A t v)). Qed.
Lemma lem4832419 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832420 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4832419 (A -> Prop) P x). Qed.
Lemma lem4832421 {A : Type'} (s : type686 A) (u : A -> Prop) : (@IN (A -> Prop) u s) = (s u).
Proof. exact (@lem4832420 A s u). Qed.
Lemma lem4832422 {A : Type'} (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term470 A v t u s) = (term494 A t v s u).
Proof. exact (MK_COMB (@lem4832417 A t v) (@lem4832421 A s u)). Qed.
Lemma lem4832425 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term471 A z v t u s) = (term495 A z t v s u).
Proof. exact (MK_COMB (@lem4832409 A u z) (@lem4832422 A t v s u)). Qed.
Lemma lem4832428 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term472 A z v t u s) = (term496 A z t v s u).
Proof. exact (MK_COMB (@lem4832401 A v z) (@lem4832425 A z t v s u)). Qed.
Lemma lem4832431 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term477 A z v t u s) = (term497 A z t v s u).
Proof. exact (MK_COMB (@lem4832393 A u v) (@lem4832428 A z t v s u)). Qed.
Lemma lem4832434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4832435 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term479 A z v t u s) = (term498 A z t v s u).
Proof. exact (MK_COMB (@lem4832434) (@lem4832431 A z t v s u)). Qed.
Lemma lem4832445 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A x s t) = (term38 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem4832446 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term37 A x s t) = (term38 A s x t).
Proof. exact (@lem4832445 A s x t). Qed.
Lemma lem4832447 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term37 A x u v) = (term38 A u x v).
Proof. exact (@lem4832446 A u x v). Qed.
Lemma lem4832451 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832452 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4832451 A P x). Qed.
Lemma lem4832453 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem4832452 A u x). Qed.
Lemma lem4832454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832455 {A : Type'} (u : A -> Prop) (x : A) : (term491 A x u) = (term492 A u x).
Proof. exact (MK_COMB (@lem4832454) (@lem4832453 A u x)). Qed.
Lemma lem4832457 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832458 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4832457 A P x). Qed.
Lemma lem4832459 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem4832458 A v x). Qed.
Lemma lem4832460 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term38 A u x v) = (term499 A u v x).
Proof. exact (MK_COMB (@lem4832455 A u x) (@lem4832459 A v x)). Qed.
Lemma lem4832463 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term37 A x u v) = (term499 A u v x).
Proof. exact (TRANS (@lem4832447 A u x v) (@lem4832460 A u v x)). Qed.
Lemma lem4832464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4832465 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term500 A x u v) = (term501 A u v x).
Proof. exact (MK_COMB (@lem4832464) (@lem4832463 A u v x)). Qed.
Lemma lem4832467 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4832468 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4832467 A x). Qed.
Lemma lem4832469 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term37 A x u v) = (@IN A x (@EMPTY A))) = ((term499 A u v x) = False).
Proof. exact (MK_COMB (@lem4832465 A u v x) (@lem4832468 A x)). Qed.
Lemma lem4832471 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4832472 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term499 A u v x) = False) = (term502 A u v x).
Proof. exact (@lem4832471 (term499 A u v x)). Qed.
Lemma lem4832475 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term37 A x u v) = (@IN A x (@EMPTY A))) = (term502 A u v x).
Proof. exact (TRANS (@lem4832469 A u v x) (@lem4832472 A u v x)). Qed.
Lemma lem4832476 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term503 A u v) = (term504 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832475 A u v x)). Qed.
Lemma lem4832477 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4832478 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term480 A u v) = (term505 A u v).
Proof. exact (MK_COMB (@lem4832477 A) (@lem4832476 A u v)). Qed.
Lemma lem4832483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4832484 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term481 A u v) = (term506 A u v).
Proof. exact (MK_COMB (@lem4832483) (@lem4832478 A u v)). Qed.
Lemma lem4832494 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832495 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4832494 (A -> Prop) P x). Qed.
Lemma lem4832496 {A : Type'} (s : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t s) = (s t).
Proof. exact (@lem4832495 A s t). Qed.
Lemma lem4832497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832498 {A : Type'} (s : type686 A) (t : A -> Prop) : (term118 A t s) = (term493 A s t).
Proof. exact (MK_COMB (@lem4832497) (@lem4832496 A s t)). Qed.
Lemma lem4832500 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832501 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4832500 (A -> Prop) P x). Qed.
Lemma lem4832502 {A : Type'} (t : type686 A) (t' : A -> Prop) : (@IN (A -> Prop) t' t) = (t t').
Proof. exact (@lem4832501 A t t'). Qed.
Lemma lem4832503 {A : Type'} (s : type686 A) (t : type686 A) (t' : A -> Prop) : (term230 A s t' t) = (term507 A s t t').
Proof. exact (MK_COMB (@lem4832498 A s t') (@lem4832502 A t t')). Qed.
Lemma lem4832506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832507 {A : Type'} (s : type686 A) (t : type686 A) (t' : A -> Prop) : (term232 A s t' t) = (term508 A s t t').
Proof. exact (MK_COMB (@lem4832506) (@lem4832503 A s t t')). Qed.
Lemma lem4832509 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4832510 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4832509 A P x). Qed.
Lemma lem4832511 {A : Type'} (t : A -> Prop) (z : A) : (@IN A z t) = (t z).
Proof. exact (@lem4832510 A t z). Qed.
Lemma lem4832512 {A : Type'} (s : type686 A) (t : type686 A) (t' : A -> Prop) (z : A) : (term234 A s t z t') = (term509 A s t t' z).
Proof. exact (MK_COMB (@lem4832507 A s t t') (@lem4832511 A t' z)). Qed.
Lemma lem4832515 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term236 A s t z) = (term510 A s t z).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4832512 A s t t' z)). Qed.
Lemma lem4832516 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4832517 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term237 A s t z) = (term511 A s t z).
Proof. exact (MK_COMB (@lem4832516 A) (@lem4832515 A s t z)). Qed.
Lemma lem4832522 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term482 A u v s t z) = (term512 A u v s t z).
Proof. exact (MK_COMB (@lem4832484 A u v) (@lem4832517 A s t z)). Qed.
Lemma lem4832525 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term484 A u v s t z) = (term513 A u v s t z).
Proof. exact (MK_COMB (@lem4832435 A z t v s u) (@lem4832522 A u v s t z)). Qed.
Lemma lem4832528 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term513 A u v s t z) = (term484 A u v s t z).
Proof. exact (SYM (@lem4832525 A u v s t z)). Qed.
Lemma lem4832530 (p : Prop) : p = (term295 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4832531 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term513 A u v s t z) = (term514 A u v s t z).
Proof. exact (@lem4832530 (term513 A u v s t z)). Qed.
Lemma lem4832532 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term514 A u v s t z) = (term513 A u v s t z).
Proof. exact (SYM (@lem4832531 A u v s t z)). Qed.
Lemma lem4832533 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term515 A u v s t z) : term515 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4832536 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term514 A u v s t z) : term514 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4832537 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term516 A u v s t z.
Proof. exact (fun h0 : term514 A u v s t z => @lem4832536 A u v s t z h0). Qed.
Lemma lem4832538 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term516 A u v s t z) : term516 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4832539 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term514 A u v s t z) : term514 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4832540 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term514 A u v s t z) (h2 : term516 A u v s t z) : term514 A u v s t z.
Proof. exact (@lem4832538 A u v s t z h2 (@lem4832539 A u v s t z h1)). Qed.
Lemma lem4832541 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term514 A u v s t z) : term517 A u v s t z.
Proof. exact (fun h0 : term516 A u v s t z => @lem4832540 A u v s t z h1 h0). Qed.
Lemma lem4832542 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term516 A u v s t z) : term516 A u v s t z.
Proof. exact (h1). Qed.
Lemma lem4832543 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term514 A u v s t z) (h2 : term516 A u v s t z) : term514 A u v s t z.
Proof. exact (@lem4832541 A u v s t z h1 (@lem4832542 A u v s t z h2)). Qed.
Lemma lem4832544 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term516 A u v s t z) : term516 A u v s t z.
Proof. exact (fun h0 : term514 A u v s t z => @lem4832543 A u v s t z h0 h1). Qed.
Lemma lem4832545 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term518 A u v s t z.
Proof. exact (fun h0 : term516 A u v s t z => @lem4832544 A u v s t z h0). Qed.
Lemma lem4832548 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term516 A u v s t z.
Proof. exact (@lem4832545 A u v s t z (@lem4832537 A u v s t z)). Qed.
Lemma lem4832549 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term516 A u v s t z.
Proof. exact (@lem4832548 A u v s t z). Qed.
Lemma lem4832571 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4832572 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term514 A u v s t z) = (term519 A u v s t z).
Proof. exact (@lem4832571 (term515 A u v s t z)). Qed.
Lemma lem4832574 (t : Prop) : (term303 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4832575 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term519 A u v s t z) = (term513 A u v s t z).
Proof. exact (@lem4832574 (term513 A u v s t z)). Qed.
Lemma lem4832578 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term514 A u v s t z) = (term513 A u v s t z).
Proof. exact (TRANS (@lem4832572 A u v s t z) (@lem4832575 A u v s t z)). Qed.
Lemma lem4832651 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term520 A v s t z) = (term521 A v s t z).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4832578 A u v s t z)). Qed.
Lemma lem4832652 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4832653 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term522 A v s t z) = (term523 A v s t z).
Proof. exact (MK_COMB (@lem4832652 A) (@lem4832651 A v s t z)). Qed.
Lemma lem4832658 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term524 A s t z) = (term525 A s t z).
Proof. exact (fun_ext (fun v : A -> Prop => @lem4832653 A v s t z)). Qed.
Lemma lem4832659 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4832660 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term526 A s t z) = (term527 A s t z).
Proof. exact (MK_COMB (@lem4832659 A) (@lem4832658 A s t z)). Qed.
Lemma lem4832665 {A : Type'} (t : type686 A) (z : A) : (term528 A t z) = (term529 A t z).
Proof. exact (fun_ext (fun s : type686 A => @lem4832660 A s t z)). Qed.
Lemma lem4832666 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4832667 {A : Type'} (t : type686 A) (z : A) : (term530 A t z) = (term531 A t z).
Proof. exact (MK_COMB (@lem4832666 A) (@lem4832665 A t z)). Qed.
Lemma lem4832672 {A : Type'} (z : A) : (term532 A z) = (term533 A z).
Proof. exact (fun_ext (fun t : type686 A => @lem4832667 A t z)). Qed.
Lemma lem4832673 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4832674 {A : Type'} (z : A) : (term534 A z) = (term535 A z).
Proof. exact (MK_COMB (@lem4832673 A) (@lem4832672 A z)). Qed.
Lemma lem4832679 {A : Type'} : (term536 A) = (term537 A).
Proof. exact (fun_ext (fun z : A => @lem4832674 A z)). Qed.
Lemma lem4832680 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4832689 {A : Type'} : (term538 A) = (term539 A).
Proof. exact (MK_COMB (@lem4832680 A) (@lem4832679 A)). Qed.
Lemma lem4832698 {A : Type'} (s : type686 A) (t : type686 A) (t' : A -> Prop) (z : A) : (term509 A s t t' z) = (term509 A s t t' z).
Proof. exact (eq_refl (term509 A s t t' z)). Qed.
Lemma lem4832699 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term510 A s t z) = (term510 A s t z).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4832698 A s t t' z)). Qed.
Lemma lem4832700 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4832701 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term511 A s t z) = (term511 A s t z).
Proof. exact (MK_COMB (@lem4832700 A) (@lem4832699 A s t z)). Qed.
Lemma lem4832708 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term502 A u v x) = (term502 A u v x).
Proof. exact (eq_refl (term502 A u v x)). Qed.
Lemma lem4832709 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term504 A u v) = (term504 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832708 A u v x)). Qed.
Lemma lem4832710 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4832711 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term505 A u v) = (term505 A u v).
Proof. exact (MK_COMB (@lem4832710 A) (@lem4832709 A u v)). Qed.
Lemma lem4832712 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4832713 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term506 A u v) = (term506 A u v).
Proof. exact (MK_COMB (@lem4832712) (@lem4832711 A u v)). Qed.
Lemma lem4832714 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term512 A u v s t z) = (term512 A u v s t z).
Proof. exact (MK_COMB (@lem4832713 A u v) (@lem4832701 A s t z)). Qed.
Lemma lem4832727 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term496 A z t v s u) = (term496 A z t v s u).
Proof. exact (eq_refl (term496 A z t v s u)). Qed.
Lemma lem4832732 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((u x) = (v x)) = ((u x) = (v x)).
Proof. exact (eq_refl ((u x) = (v x))). Qed.
Lemma lem4832733 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term487 A u v) = (term487 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832732 A u v x)). Qed.
Lemma lem4832734 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4832735 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term488 A u v) = (term488 A u v).
Proof. exact (MK_COMB (@lem4832734 A) (@lem4832733 A u v)). Qed.
Lemma lem4832736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4832737 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term489 A u v) = (term489 A u v).
Proof. exact (MK_COMB (@lem4832736) (@lem4832735 A u v)). Qed.
Lemma lem4832738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832739 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term490 A u v) = (term490 A u v).
Proof. exact (MK_COMB (@lem4832738) (@lem4832737 A u v)). Qed.
Lemma lem4832740 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term497 A z t v s u) = (term497 A z t v s u).
Proof. exact (MK_COMB (@lem4832739 A u v) (@lem4832727 A z t v s u)). Qed.
Lemma lem4832741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4832742 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term498 A z t v s u) = (term498 A z t v s u).
Proof. exact (MK_COMB (@lem4832741) (@lem4832740 A z t v s u)). Qed.
Lemma lem4832743 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term513 A u v s t z) = (term513 A u v s t z).
Proof. exact (MK_COMB (@lem4832742 A z t v s u) (@lem4832714 A u v s t z)). Qed.
Lemma lem4832744 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term521 A v s t z) = (term521 A v s t z).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4832743 A u v s t z)). Qed.
Lemma lem4832745 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4832746 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term523 A v s t z) = (term523 A v s t z).
Proof. exact (MK_COMB (@lem4832745 A) (@lem4832744 A v s t z)). Qed.
Lemma lem4832747 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term525 A s t z) = (term525 A s t z).
Proof. exact (fun_ext (fun v : A -> Prop => @lem4832746 A v s t z)). Qed.
Lemma lem4832748 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4832749 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term527 A s t z) = (term527 A s t z).
Proof. exact (MK_COMB (@lem4832748 A) (@lem4832747 A s t z)). Qed.
Lemma lem4832750 {A : Type'} (t : type686 A) (z : A) : (term529 A t z) = (term529 A t z).
Proof. exact (fun_ext (fun s : type686 A => @lem4832749 A s t z)). Qed.
Lemma lem4832751 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4832752 {A : Type'} (t : type686 A) (z : A) : (term531 A t z) = (term531 A t z).
Proof. exact (MK_COMB (@lem4832751 A) (@lem4832750 A t z)). Qed.
Lemma lem4832753 {A : Type'} (z : A) : (term533 A z) = (term533 A z).
Proof. exact (fun_ext (fun t : type686 A => @lem4832752 A t z)). Qed.
Lemma lem4832754 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4832755 {A : Type'} (z : A) : (term535 A z) = (term535 A z).
Proof. exact (MK_COMB (@lem4832754 A) (@lem4832753 A z)). Qed.
Lemma lem4832756 {A : Type'} : (term537 A) = (term537 A).
Proof. exact (fun_ext (fun z : A => @lem4832755 A z)). Qed.
Lemma lem4832757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4832758 {A : Type'} : (term539 A) = (term539 A).
Proof. exact (MK_COMB (@lem4832757 A) (@lem4832756 A)). Qed.
Lemma lem4832827 {A : Type'} : (term538 A) = (term539 A).
Proof. exact (TRANS (@lem4832689 A) (@lem4832758 A)). Qed.
Lemma lem4832828 {A : Type'} : (term539 A) = (term538 A).
Proof. exact (SYM (@lem4832827 A)). Qed.
Lemma lem4832829 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term497 A z t v s u) : term497 A z t v s u.
Proof. exact (h1). Qed.
Lemma lem4832830 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term505 A u v.
Proof. exact (h1). Qed.
Lemma lem4832832 (p : Prop) : p = (term295 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4832833 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term511 A s t z) = (term540 A s t z).
Proof. exact (@lem4832832 (term511 A s t z)). Qed.
Lemma lem4832834 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term540 A s t z) = (term511 A s t z).
Proof. exact (SYM (@lem4832833 A s t z)). Qed.
Lemma lem4832850 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term541 A u v x) = (term542 A u v x).
Proof. exact (@lem17646 (u x) (v x)). Qed.
Lemma lem4832851 {A : Type'} (P : A -> Prop) : (term543 A P) = (term544 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4832852 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term489 A u v) = (term545 A u v).
Proof. exact (@lem4832851 A (term487 A u v)). Qed.
Lemma lem4832853 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term546 A u v x) = ((u x) = (v x)).
Proof. exact (eq_refl (term546 A u v x)). Qed.
Lemma lem4832854 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4832855 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term547 A u v x) = (term541 A u v x).
Proof. exact (MK_COMB (@lem4832854) (@lem4832853 A u v x)). Qed.
Lemma lem4832856 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term547 A u v x) = (term542 A u v x).
Proof. exact (TRANS (@lem4832855 A u v x) (@lem4832850 A u v x)). Qed.
Lemma lem4832857 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term548 A u v) = (term549 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832856 A u v x)). Qed.
Lemma lem4832858 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4832859 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term545 A u v) = (term550 A u v).
Proof. exact (MK_COMB (@lem4832858 A) (@lem4832857 A u v)). Qed.
Lemma lem4832860 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term489 A u v) = (term550 A u v).
Proof. exact (TRANS (@lem4832852 A u v) (@lem4832859 A u v)). Qed.
Lemma lem4832873 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term496 A z t v s u) = (term496 A z t v s u).
Proof. exact (eq_refl (term496 A z t v s u)). Qed.
Lemma lem4832874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832875 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term490 A u v) = (term551 A u v).
Proof. exact (MK_COMB (@lem4832874) (@lem4832860 A u v)). Qed.
Lemma lem4832876 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term497 A z t v s u) = (term552 A z t v s u).
Proof. exact (MK_COMB (@lem4832875 A u v) (@lem4832873 A z t v s u)). Qed.
Lemma lem4832878 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4832879 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (@lem4832878 A P Q). Qed.
Lemma lem4832880 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term555 A u v) = (term556 A u v).
Proof. exact (@lem4832879 A (term557 A u v) (term558 A u v)). Qed.
Lemma lem4832881 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term559 A u v x) = (term560 A u v x).
Proof. exact (eq_refl (term559 A u v x)). Qed.
Lemma lem4832882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4832883 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term561 A u v x) = (term562 A u v x).
Proof. exact (MK_COMB (@lem4832882) (@lem4832881 A u v x)). Qed.
Lemma lem4832884 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term563 A u v x) = (term564 A u v x).
Proof. exact (eq_refl (term563 A u v x)). Qed.
Lemma lem4832885 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term565 A u v x) = (term542 A u v x).
Proof. exact (MK_COMB (@lem4832883 A u v x) (@lem4832884 A u v x)). Qed.
Lemma lem4832886 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term566 A u v) = (term549 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832885 A u v x)). Qed.
Lemma lem4832887 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4832888 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term555 A u v) = (term550 A u v).
Proof. exact (MK_COMB (@lem4832887 A) (@lem4832886 A u v)). Qed.
Lemma lem4832889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4832890 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term567 A u v) = (term568 A u v).
Proof. exact (MK_COMB (@lem4832889) (@lem4832888 A u v)). Qed.
Lemma lem4832891 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term559 A u v x) = (term560 A u v x).
Proof. exact (eq_refl (term559 A u v x)). Qed.
Lemma lem4832892 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term569 A u v) = (term557 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832891 A u v x)). Qed.
Lemma lem4832893 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4832894 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term570 A u v) = (term571 A u v).
Proof. exact (MK_COMB (@lem4832893 A) (@lem4832892 A u v)). Qed.
Lemma lem4832895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4832896 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term572 A u v) = (term573 A u v).
Proof. exact (MK_COMB (@lem4832895) (@lem4832894 A u v)). Qed.
Lemma lem4832897 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term563 A u v x) = (term564 A u v x).
Proof. exact (eq_refl (term563 A u v x)). Qed.
Lemma lem4832898 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term574 A u v) = (term558 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832897 A u v x)). Qed.
Lemma lem4832899 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4832900 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term575 A u v) = (term576 A u v).
Proof. exact (MK_COMB (@lem4832899 A) (@lem4832898 A u v)). Qed.
Lemma lem4832901 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term556 A u v) = (term577 A u v).
Proof. exact (MK_COMB (@lem4832896 A u v) (@lem4832900 A u v)). Qed.
Lemma lem4832902 {A : Type'} (u : A -> Prop) (v : A -> Prop) : ((term555 A u v) = (term556 A u v)) = ((term550 A u v) = (term577 A u v)).
Proof. exact (MK_COMB (@lem4832890 A u v) (@lem4832901 A u v)). Qed.
Lemma lem4832903 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term550 A u v) = (term577 A u v).
Proof. exact (EQ_MP (@lem4832902 A u v) (@lem4832880 A u v)). Qed.
Lemma lem4832964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832965 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term551 A u v) = (term578 A u v).
Proof. exact (MK_COMB (@lem4832964) (@lem4832903 A u v)). Qed.
Lemma lem4832966 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term496 A z t v s u) = (term496 A z t v s u).
Proof. exact (eq_refl (term496 A z t v s u)). Qed.
Lemma lem4832967 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term552 A z t v s u) = (term579 A z t v s u).
Proof. exact (MK_COMB (@lem4832965 A u v) (@lem4832966 A z t v s u)). Qed.
Lemma lem4832969 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4832970 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term553 A P Q).
Proof. exact (@lem4832969 A P Q). Qed.
Lemma lem4832971 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term556 A u v) = (term555 A u v).
Proof. exact (@lem4832970 A (term557 A u v) (term558 A u v)). Qed.
Lemma lem4832972 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term559 A u v x) = (term560 A u v x).
Proof. exact (eq_refl (term559 A u v x)). Qed.
Lemma lem4832973 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term569 A u v) = (term557 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832972 A u v x)). Qed.
Lemma lem4832974 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4832975 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term570 A u v) = (term571 A u v).
Proof. exact (MK_COMB (@lem4832974 A) (@lem4832973 A u v)). Qed.
Lemma lem4832976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4832977 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term572 A u v) = (term573 A u v).
Proof. exact (MK_COMB (@lem4832976) (@lem4832975 A u v)). Qed.
Lemma lem4832978 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term563 A u v x) = (term564 A u v x).
Proof. exact (eq_refl (term563 A u v x)). Qed.
Lemma lem4832979 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term574 A u v) = (term558 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832978 A u v x)). Qed.
Lemma lem4832980 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4832981 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term575 A u v) = (term576 A u v).
Proof. exact (MK_COMB (@lem4832980 A) (@lem4832979 A u v)). Qed.
Lemma lem4832982 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term556 A u v) = (term577 A u v).
Proof. exact (MK_COMB (@lem4832977 A u v) (@lem4832981 A u v)). Qed.
Lemma lem4832983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4832984 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term580 A u v) = (term581 A u v).
Proof. exact (MK_COMB (@lem4832983) (@lem4832982 A u v)). Qed.
Lemma lem4832985 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term559 A u v x) = (term560 A u v x).
Proof. exact (eq_refl (term559 A u v x)). Qed.
Lemma lem4832986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4832987 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term561 A u v x) = (term562 A u v x).
Proof. exact (MK_COMB (@lem4832986) (@lem4832985 A u v x)). Qed.
Lemma lem4832988 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term563 A u v x) = (term564 A u v x).
Proof. exact (eq_refl (term563 A u v x)). Qed.
Lemma lem4832989 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term565 A u v x) = (term542 A u v x).
Proof. exact (MK_COMB (@lem4832987 A u v x) (@lem4832988 A u v x)). Qed.
Lemma lem4832990 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term566 A u v) = (term549 A u v).
Proof. exact (fun_ext (fun x : A => @lem4832989 A u v x)). Qed.
Lemma lem4832991 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4832992 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term555 A u v) = (term550 A u v).
Proof. exact (MK_COMB (@lem4832991 A) (@lem4832990 A u v)). Qed.
Lemma lem4832993 {A : Type'} (u : A -> Prop) (v : A -> Prop) : ((term556 A u v) = (term555 A u v)) = ((term577 A u v) = (term550 A u v)).
Proof. exact (MK_COMB (@lem4832984 A u v) (@lem4832992 A u v)). Qed.
Lemma lem4832994 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term577 A u v) = (term550 A u v).
Proof. exact (EQ_MP (@lem4832993 A u v) (@lem4832971 A u v)). Qed.
Lemma lem4832995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4832996 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term578 A u v) = (term551 A u v).
Proof. exact (MK_COMB (@lem4832995) (@lem4832994 A u v)). Qed.
Lemma lem4832997 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term496 A z t v s u) = (term496 A z t v s u).
Proof. exact (eq_refl (term496 A z t v s u)). Qed.
Lemma lem4832998 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term579 A z t v s u) = (term552 A z t v s u).
Proof. exact (MK_COMB (@lem4832996 A u v) (@lem4832997 A z t v s u)). Qed.
Lemma lem4833000 {A : Type'} (P : A -> Prop) (Q : Prop) : (term582 A P Q) = (term583 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4833001 {A : Type'} (P : A -> Prop) (Q : Prop) : (term582 A P Q) = (term583 A P Q).
Proof. exact (@lem4833000 A P Q). Qed.
Lemma lem4833002 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term584 A z t v s u) = (term585 A z t v s u).
Proof. exact (@lem4833001 A (term549 A u v) (term496 A z t v s u)). Qed.
Lemma lem4833003 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term586 A u v x) = (term542 A u v x).
Proof. exact (eq_refl (term586 A u v x)). Qed.
Lemma lem4833004 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term587 A u v) = (term549 A u v).
Proof. exact (fun_ext (fun x : A => @lem4833003 A u v x)). Qed.
Lemma lem4833005 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4833006 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term588 A u v) = (term550 A u v).
Proof. exact (MK_COMB (@lem4833005 A) (@lem4833004 A u v)). Qed.
Lemma lem4833007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833008 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term589 A u v) = (term551 A u v).
Proof. exact (MK_COMB (@lem4833007) (@lem4833006 A u v)). Qed.
Lemma lem4833009 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term496 A z t v s u) = (term496 A z t v s u).
Proof. exact (eq_refl (term496 A z t v s u)). Qed.
Lemma lem4833010 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term584 A z t v s u) = (term552 A z t v s u).
Proof. exact (MK_COMB (@lem4833008 A u v) (@lem4833009 A z t v s u)). Qed.
Lemma lem4833011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4833012 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term590 A z t v s u) = (term591 A z t v s u).
Proof. exact (MK_COMB (@lem4833011) (@lem4833010 A z t v s u)). Qed.
Lemma lem4833013 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term586 A u v x) = (term542 A u v x).
Proof. exact (eq_refl (term586 A u v x)). Qed.
Lemma lem4833014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833015 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term592 A u v x) = (term593 A u v x).
Proof. exact (MK_COMB (@lem4833014) (@lem4833013 A u v x)). Qed.
Lemma lem4833016 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term496 A z t v s u) = (term496 A z t v s u).
Proof. exact (eq_refl (term496 A z t v s u)). Qed.
Lemma lem4833017 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term594 A x z t v s u) = (term595 A x z t v s u).
Proof. exact (MK_COMB (@lem4833015 A u v x) (@lem4833016 A z t v s u)). Qed.
Lemma lem4833018 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term596 A z t v s u) = (term597 A z t v s u).
Proof. exact (fun_ext (fun x : A => @lem4833017 A x z t v s u)). Qed.
Lemma lem4833019 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4833020 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term585 A z t v s u) = (term598 A z t v s u).
Proof. exact (MK_COMB (@lem4833019 A) (@lem4833018 A z t v s u)). Qed.
Lemma lem4833021 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : ((term584 A z t v s u) = (term585 A z t v s u)) = ((term552 A z t v s u) = (term598 A z t v s u)).
Proof. exact (MK_COMB (@lem4833012 A z t v s u) (@lem4833020 A z t v s u)). Qed.
Lemma lem4833022 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term552 A z t v s u) = (term598 A z t v s u).
Proof. exact (EQ_MP (@lem4833021 A z t v s u) (@lem4833002 A z t v s u)). Qed.
Lemma lem4833023 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term579 A z t v s u) = (term598 A z t v s u).
Proof. exact (TRANS (@lem4832998 A z t v s u) (@lem4833022 A z t v s u)). Qed.
Lemma lem4833024 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term552 A z t v s u) = (term598 A z t v s u).
Proof. exact (TRANS (@lem4832967 A z t v s u) (@lem4833023 A z t v s u)). Qed.
Lemma lem4833025 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term497 A z t v s u) = (term598 A z t v s u).
Proof. exact (TRANS (@lem4832876 A z t v s u) (@lem4833024 A z t v s u)). Qed.
Lemma lem4833026 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term497 A z t v s u) : term598 A z t v s u.
Proof. exact (EQ_MP (@lem4833025 A z t v s u) (@lem4832829 A z t v s u h1)). Qed.
Lemma lem4833033 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term502 A u v x) = (term599 A u v x).
Proof. exact (@lem17045 (u x) (v x)). Qed.
Lemma lem4833034 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term504 A u v) = (term600 A u v).
Proof. exact (fun_ext (fun x : A => @lem4833033 A u v x)). Qed.
Lemma lem4833035 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4833088 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term505 A u v) = (term601 A u v).
Proof. exact (MK_COMB (@lem4833035 A) (@lem4833034 A u v)). Qed.
Lemma lem4833089 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term601 A u v.
Proof. exact (EQ_MP (@lem4833088 A u v) (@lem4832830 A u v h1)). Qed.
Lemma lem4833166 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term595 A x z t v s u.
Proof. exact (h1). Qed.
Lemma lem4833167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833172 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833173 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4833172 A Prop f x). Qed.
Lemma lem4833175 {A : Type'} (v : A -> Prop) (x : A) : (v x) = (@I (A -> Prop) v x).
Proof. exact (@lem4833173 A v x). Qed.
Lemma lem4833176 {A : Type'} (v : A -> Prop) (x : A) : (term602 A v x) = (term603 A v x).
Proof. exact (MK_COMB (@lem4833167) (@lem4833175 A v x)). Qed.
Lemma lem4833177 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833183 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4833182 A Prop f x). Qed.
Lemma lem4833185 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem4833183 A u x). Qed.
Lemma lem4833186 {A : Type'} (u : A -> Prop) (x : A) : (term602 A u x) = (term603 A u x).
Proof. exact (MK_COMB (@lem4833177) (@lem4833185 A u x)). Qed.
Lemma lem4833187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4833188 {A : Type'} (u : A -> Prop) (x : A) : (term604 A u x) = (term605 A u x).
Proof. exact (MK_COMB (@lem4833187) (@lem4833186 A u x)). Qed.
Lemma lem4833189 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term599 A u v x) = (term606 A u v x).
Proof. exact (MK_COMB (@lem4833188 A u x) (@lem4833176 A v x)). Qed.
Lemma lem4833190 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term600 A u v) = (term607 A u v).
Proof. exact (fun_ext (fun x : A => @lem4833189 A u v x)). Qed.
Lemma lem4833191 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4833192 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term601 A u v) = (term608 A u v).
Proof. exact (MK_COMB (@lem4833191 A) (@lem4833190 A u v)). Qed.
Lemma lem4833193 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term608 A u v.
Proof. exact (EQ_MP (@lem4833192 A u v) (@lem4833089 A u v h1)). Qed.
Lemma lem4833238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833239 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4833238 (A -> Prop) Prop f x). Qed.
Lemma lem4833241 {A : Type'} (s : type686 A) (u : A -> Prop) : (s u) = (@I ((A -> Prop) -> Prop) s u).
Proof. exact (@lem4833239 A s u). Qed.
Lemma lem4833246 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833247 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4833246 (A -> Prop) Prop f x). Qed.
Lemma lem4833249 {A : Type'} (t : type686 A) (v : A -> Prop) : (t v) = (@I ((A -> Prop) -> Prop) t v).
Proof. exact (@lem4833247 A t v). Qed.
Lemma lem4833250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833251 {A : Type'} (t : type686 A) (v : A -> Prop) : (term493 A t v) = (term609 A t v).
Proof. exact (MK_COMB (@lem4833250) (@lem4833249 A t v)). Qed.
Lemma lem4833252 {A : Type'} (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term494 A t v s u) = (term610 A t v s u).
Proof. exact (MK_COMB (@lem4833251 A t v) (@lem4833241 A s u)). Qed.
Lemma lem4833257 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833258 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4833257 A Prop f x). Qed.
Lemma lem4833260 {A : Type'} (u : A -> Prop) (z : A) : (u z) = (@I (A -> Prop) u z).
Proof. exact (@lem4833258 A u z). Qed.
Lemma lem4833261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833262 {A : Type'} (u : A -> Prop) (z : A) : (term492 A u z) = (term611 A u z).
Proof. exact (MK_COMB (@lem4833261) (@lem4833260 A u z)). Qed.
Lemma lem4833263 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term495 A z t v s u) = (term612 A z t v s u).
Proof. exact (MK_COMB (@lem4833262 A u z) (@lem4833252 A t v s u)). Qed.
Lemma lem4833268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833269 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4833268 A Prop f x). Qed.
Lemma lem4833271 {A : Type'} (v : A -> Prop) (z : A) : (v z) = (@I (A -> Prop) v z).
Proof. exact (@lem4833269 A v z). Qed.
Lemma lem4833272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833273 {A : Type'} (v : A -> Prop) (z : A) : (term492 A v z) = (term611 A v z).
Proof. exact (MK_COMB (@lem4833272) (@lem4833271 A v z)). Qed.
Lemma lem4833274 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term496 A z t v s u) = (term613 A z t v s u).
Proof. exact (MK_COMB (@lem4833273 A v z) (@lem4833263 A z t v s u)). Qed.
Lemma lem4833279 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833280 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4833279 A Prop f x). Qed.
Lemma lem4833282 {A : Type'} (v : A -> Prop) (x : A) : (v x) = (@I (A -> Prop) v x).
Proof. exact (@lem4833280 A v x). Qed.
Lemma lem4833283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833288 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833289 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4833288 A Prop f x). Qed.
Lemma lem4833291 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem4833289 A u x). Qed.
Lemma lem4833292 {A : Type'} (u : A -> Prop) (x : A) : (term602 A u x) = (term603 A u x).
Proof. exact (MK_COMB (@lem4833283) (@lem4833291 A u x)). Qed.
Lemma lem4833293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833294 {A : Type'} (u : A -> Prop) (x : A) : (term614 A u x) = (term615 A u x).
Proof. exact (MK_COMB (@lem4833293) (@lem4833292 A u x)). Qed.
Lemma lem4833295 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term564 A u v x) = (term616 A u v x).
Proof. exact (MK_COMB (@lem4833294 A u x) (@lem4833282 A v x)). Qed.
Lemma lem4833296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833302 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4833301 A Prop f x). Qed.
Lemma lem4833304 {A : Type'} (v : A -> Prop) (x : A) : (v x) = (@I (A -> Prop) v x).
Proof. exact (@lem4833302 A v x). Qed.
Lemma lem4833305 {A : Type'} (v : A -> Prop) (x : A) : (term602 A v x) = (term603 A v x).
Proof. exact (MK_COMB (@lem4833296) (@lem4833304 A v x)). Qed.
Lemma lem4833310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4833311 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4833310 A Prop f x). Qed.
Lemma lem4833313 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem4833311 A u x). Qed.
Lemma lem4833314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833315 {A : Type'} (u : A -> Prop) (x : A) : (term492 A u x) = (term611 A u x).
Proof. exact (MK_COMB (@lem4833314) (@lem4833313 A u x)). Qed.
Lemma lem4833316 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term560 A u v x) = (term617 A u v x).
Proof. exact (MK_COMB (@lem4833315 A u x) (@lem4833305 A v x)). Qed.
Lemma lem4833317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4833318 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term562 A u v x) = (term618 A u v x).
Proof. exact (MK_COMB (@lem4833317) (@lem4833316 A u v x)). Qed.
Lemma lem4833319 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term542 A u v x) = (term619 A u v x).
Proof. exact (MK_COMB (@lem4833318 A u v x) (@lem4833295 A u v x)). Qed.
Lemma lem4833320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833321 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term593 A u v x) = (term620 A u v x).
Proof. exact (MK_COMB (@lem4833320) (@lem4833319 A u v x)). Qed.
Lemma lem4833322 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) : (term595 A x z t v s u) = (term621 A x z t v s u).
Proof. exact (MK_COMB (@lem4833321 A u v x) (@lem4833274 A z t v s u)). Qed.
Lemma lem4833323 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term621 A x z t v s u.
Proof. exact (EQ_MP (@lem4833322 A x z t v s u) (@lem4833166 A x z t v s u h1)). Qed.
Lemma lem4833324 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term613 A z t v s u.
Proof. exact (proj2 (@lem4833323 A x z t v s u h1)). Qed.
Lemma lem4833325 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term619 A u v x.
Proof. exact (proj1 (@lem4833323 A x z t v s u h1)). Qed.
Lemma lem4833326 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term612 A z t v s u.
Proof. exact (proj2 (@lem4833324 A x z t v s u h1)). Qed.
Lemma lem4833345 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term606 A u v x) = (term606 A u v x).
Proof. exact (eq_refl (term606 A u v x)). Qed.
Lemma lem4833346 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term607 A u v) = (term607 A u v).
Proof. exact (fun_ext (fun x : A => @lem4833345 A u v x)). Qed.
Lemma lem4833347 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4833349 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term608 A u v) = (term608 A u v).
Proof. exact (MK_COMB (@lem4833347 A) (@lem4833346 A u v)). Qed.
Lemma lem4833350 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term608 A u v.
Proof. exact (EQ_MP (@lem4833349 A u v) (@lem4833193 A u v h1)). Qed.
Lemma lem4833401 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term606 A u v x) = (term606 A u v x).
Proof. exact (eq_refl (term606 A u v x)). Qed.
Lemma lem4833402 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term607 A u v) = (term607 A u v).
Proof. exact (fun_ext (fun x : A => @lem4833401 A u v x)). Qed.
Lemma lem4833403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4833405 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term608 A u v) = (term608 A u v).
Proof. exact (MK_COMB (@lem4833403 A) (@lem4833402 A u v)). Qed.
Lemma lem4833406 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term608 A u v.
Proof. exact (EQ_MP (@lem4833405 A u v) (@lem4833193 A u v h1)). Qed.
Lemma lem4833450 {A : Type'} (_59855 : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term622 A u v _59855.
Proof. exact (@lem4833350 A u v h1 _59855). Qed.
Lemma lem4833451 {A : Type'} (u : A -> Prop) (v : A -> Prop) (_59855 : A) : (term622 A u v _59855) = (term606 A u v _59855).
Proof. exact (eq_refl (term622 A u v _59855)). Qed.
Lemma lem4833456 {A : Type'} (_59857 : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term622 A u v _59857.
Proof. exact (@lem4833406 A u v h1 _59857). Qed.
Lemma lem4833457 {A : Type'} (u : A -> Prop) (v : A -> Prop) (_59857 : A) : (term622 A u v _59857) = (term606 A u v _59857).
Proof. exact (eq_refl (term622 A u v _59857)). Qed.
Lemma lem4833467 {A : Type'} (_59855 : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term606 A u v _59855.
Proof. exact (EQ_MP (@lem4833451 A u v _59855) (@lem4833450 A _59855 u v h1)). Qed.
Lemma lem4833497 {A : Type'} (_59857 : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term606 A u v _59857.
Proof. exact (EQ_MP (@lem4833457 A u v _59857) (@lem4833456 A _59857 u v h1)). Qed.
Lemma lem4833523 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : @I (A -> Prop) u z.
Proof. exact (proj1 (@lem4833326 A x z t v s u h1)). Qed.
Lemma lem4833524 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term623 A u z.
Proof. exact (fun h0 : term603 A u z => @lem4833523 A x z t v s u h1). Qed.
Lemma lem4833526 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4833527 {A : Type'} (u : A -> Prop) (z : A) : (term623 A u z) = (@I (A -> Prop) u z).
Proof. exact (@lem4833526 (@I (A -> Prop) u z)). Qed.
Lemma lem4833528 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : @I (A -> Prop) u z.
Proof. exact (EQ_MP (@lem4833527 A u z) (@lem4833524 A x z t v s u h1)). Qed.
Lemma lem4833530 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : @I (A -> Prop) v z.
Proof. exact (proj1 (@lem4833324 A x z t v s u h1)). Qed.
Lemma lem4833531 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term623 A v z.
Proof. exact (fun h0 : term603 A v z => @lem4833530 A x z t v s u h1). Qed.
Lemma lem4833533 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4833534 {A : Type'} (v : A -> Prop) (z : A) : (term623 A v z) = (@I (A -> Prop) v z).
Proof. exact (@lem4833533 (@I (A -> Prop) v z)). Qed.
Lemma lem4833535 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : @I (A -> Prop) v z.
Proof. exact (EQ_MP (@lem4833534 A v z) (@lem4833531 A x z t v s u h1)). Qed.
Lemma lem4833537 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4833538 {A : Type'} (u : A -> Prop) (v : A -> Prop) (_59855 : A) : (term606 A u v _59855) = (term624 A u v _59855).
Proof. exact (@lem4833537 (@I (A -> Prop) u _59855) (@I (A -> Prop) v _59855)). Qed.
Lemma lem4833540 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4833541 {A : Type'} (u : A -> Prop) (v : A -> Prop) (_59855 : A) : (term624 A u v _59855) = (term625 A u v _59855).
Proof. exact (@lem4833540 (term626 A u v _59855)). Qed.
Lemma lem4833542 {A : Type'} (u : A -> Prop) (v : A -> Prop) (_59855 : A) : (term606 A u v _59855) = (term625 A u v _59855).
Proof. exact (TRANS (@lem4833538 A u v _59855) (@lem4833541 A u v _59855)). Qed.
Lemma lem4833544 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term626 A u v z.
Proof. exact (conj (@lem4833528 A x z t v s u h1) (@lem4833535 A x z t v s u h1)). Qed.
Lemma lem4833546 {A : Type'} (_59855 : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term625 A u v _59855.
Proof. exact (EQ_MP (@lem4833542 A u v _59855) (@lem4833467 A _59855 u v h1)). Qed.
Lemma lem4833547 {A : Type'} (_59855 : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term625 A u v _59855.
Proof. exact (@lem4833546 A _59855 u v h1). Qed.
Lemma lem4833548 {A : Type'} (z : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term625 A u v z.
Proof. exact (@lem4833547 A z u v h1). Qed.
Lemma lem4833551 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term595 A x z t v s u) : False.
Proof. exact (@lem4833548 A z u v h1 (@lem4833544 A x z t v s u h2)). Qed.
Lemma lem4833552 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term595 A x z t v s u) : term379.
Proof. exact (fun h0 : ~ False => @lem4833551 A x z t v s u h1 h2). Qed.
Lemma lem4833554 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4833555 : term379 = False.
Proof. exact (@lem4833554 False). Qed.
Lemma lem4833556 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term595 A x z t v s u) : False.
Proof. exact (EQ_MP (@lem4833555) (@lem4833552 A x z t v s u h1 h2)). Qed.
Lemma lem4833558 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : @I (A -> Prop) u z.
Proof. exact (proj1 (@lem4833326 A x z t v s u h1)). Qed.
Lemma lem4833559 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term623 A u z.
Proof. exact (fun h0 : term603 A u z => @lem4833558 A x z t v s u h1). Qed.
Lemma lem4833561 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4833562 {A : Type'} (u : A -> Prop) (z : A) : (term623 A u z) = (@I (A -> Prop) u z).
Proof. exact (@lem4833561 (@I (A -> Prop) u z)). Qed.
Lemma lem4833563 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : @I (A -> Prop) u z.
Proof. exact (EQ_MP (@lem4833562 A u z) (@lem4833559 A x z t v s u h1)). Qed.
Lemma lem4833565 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : @I (A -> Prop) v z.
Proof. exact (proj1 (@lem4833324 A x z t v s u h1)). Qed.
Lemma lem4833566 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term623 A v z.
Proof. exact (fun h0 : term603 A v z => @lem4833565 A x z t v s u h1). Qed.
Lemma lem4833568 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4833569 {A : Type'} (v : A -> Prop) (z : A) : (term623 A v z) = (@I (A -> Prop) v z).
Proof. exact (@lem4833568 (@I (A -> Prop) v z)). Qed.
Lemma lem4833570 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : @I (A -> Prop) v z.
Proof. exact (EQ_MP (@lem4833569 A v z) (@lem4833566 A x z t v s u h1)). Qed.
Lemma lem4833572 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4833573 {A : Type'} (u : A -> Prop) (v : A -> Prop) (_59857 : A) : (term606 A u v _59857) = (term624 A u v _59857).
Proof. exact (@lem4833572 (@I (A -> Prop) u _59857) (@I (A -> Prop) v _59857)). Qed.
Lemma lem4833575 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4833576 {A : Type'} (u : A -> Prop) (v : A -> Prop) (_59857 : A) : (term624 A u v _59857) = (term625 A u v _59857).
Proof. exact (@lem4833575 (term626 A u v _59857)). Qed.
Lemma lem4833577 {A : Type'} (u : A -> Prop) (v : A -> Prop) (_59857 : A) : (term606 A u v _59857) = (term625 A u v _59857).
Proof. exact (TRANS (@lem4833573 A u v _59857) (@lem4833576 A u v _59857)). Qed.
Lemma lem4833579 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term595 A x z t v s u) : term626 A u v z.
Proof. exact (conj (@lem4833563 A x z t v s u h1) (@lem4833570 A x z t v s u h1)). Qed.
Lemma lem4833581 {A : Type'} (_59857 : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term625 A u v _59857.
Proof. exact (EQ_MP (@lem4833577 A u v _59857) (@lem4833497 A _59857 u v h1)). Qed.
Lemma lem4833582 {A : Type'} (_59857 : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term625 A u v _59857.
Proof. exact (@lem4833581 A _59857 u v h1). Qed.
Lemma lem4833583 {A : Type'} (z : A) (u : A -> Prop) (v : A -> Prop) (h1 : term505 A u v) : term625 A u v z.
Proof. exact (@lem4833582 A z u v h1). Qed.
Lemma lem4833586 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term595 A x z t v s u) : False.
Proof. exact (@lem4833583 A z u v h1 (@lem4833579 A x z t v s u h2)). Qed.
Lemma lem4833587 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term595 A x z t v s u) : term379.
Proof. exact (fun h0 : ~ False => @lem4833586 A x z t v s u h1 h2). Qed.
Lemma lem4833589 (p : Prop) : (term367 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4833590 : term379 = False.
Proof. exact (@lem4833589 False). Qed.
Lemma lem4833591 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term595 A x z t v s u) : False.
Proof. exact (EQ_MP (@lem4833590) (@lem4833587 A x z t v s u h1 h2)). Qed.
Lemma lem4833592 {A : Type'} (x : A) (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term595 A x z t v s u) : False.
Proof. exact (or_elim (@lem4833325 A x z t v s u h2) (fun h0 : term617 A u v x => @lem4833556 A x z t v s u h1 h2) (fun h0 : term616 A u v x => @lem4833591 A x z t v s u h1 h2)). Qed.
Lemma lem4833593 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term497 A z t v s u) : False.
Proof. exact (ex_elim (@lem4833026 A z t v s u h2) (fun x : A => fun h0 : term597 A z t v s u x => @lem4833592 A x z t v s u h1 h0)). Qed.
Lemma lem4833594 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term497 A z t v s u) : term540 A s t z.
Proof. exact (fun h0 : term627 A s t z => @lem4833593 A z t v s u h1 h2). Qed.
Lemma lem4833595 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term505 A u v) (h2 : term497 A z t v s u) : term511 A s t z.
Proof. exact (EQ_MP (@lem4832834 A s t z) (@lem4833594 A z t v s u h1 h2)). Qed.
Lemma lem4833596 {A : Type'} (z : A) (t : type686 A) (v : A -> Prop) (s : type686 A) (u : A -> Prop) (h1 : term497 A z t v s u) : term512 A u v s t z.
Proof. exact (fun h0 : term505 A u v => @lem4833595 A z t v s u h0 h1). Qed.
Lemma lem4833597 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term513 A u v s t z.
Proof. exact (fun h0 : term497 A z t v s u => @lem4833596 A z t v s u h0). Qed.
Lemma lem4833602 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term523 A v s t z.
Proof. exact (fun u : A -> Prop => @lem4833597 A u v s t z). Qed.
Lemma lem4833607 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term527 A s t z.
Proof. exact (fun v : A -> Prop => @lem4833602 A v s t z). Qed.
Lemma lem4833612 {A : Type'} (t : type686 A) (z : A) : term531 A t z.
Proof. exact (fun s : type686 A => @lem4833607 A s t z). Qed.
Lemma lem4833617 {A : Type'} (z : A) : term535 A z.
Proof. exact (fun t : type686 A => @lem4833612 A t z). Qed.
Lemma lem4833622 {A : Type'} : term539 A.
Proof. exact (fun z : A => @lem4833617 A z). Qed.
Lemma lem4833623 {A : Type'} : term538 A.
Proof. exact (EQ_MP (@lem4832828 A) (@lem4833622 A)). Qed.
Lemma lem4833624 {A : Type'} (z : A) : term628 A z.
Proof. exact (@lem4833623 A z). Qed.
Lemma lem4833625 {A : Type'} (z : A) : (term628 A z) = (term534 A z).
Proof. exact (eq_refl (term628 A z)). Qed.
Lemma lem4833626 {A : Type'} (z : A) : term534 A z.
Proof. exact (EQ_MP (@lem4833625 A z) (@lem4833624 A z)). Qed.
Lemma lem4833627 {A : Type'} (z : A) (t : type686 A) : term629 A z t.
Proof. exact (@lem4833626 A z t). Qed.
Lemma lem4833628 {A : Type'} (t : type686 A) (z : A) : (term629 A z t) = (term530 A t z).
Proof. exact (eq_refl (term629 A z t)). Qed.
Lemma lem4833629 {A : Type'} (t : type686 A) (z : A) : term530 A t z.
Proof. exact (EQ_MP (@lem4833628 A t z) (@lem4833627 A z t)). Qed.
Lemma lem4833630 {A : Type'} (t : type686 A) (z : A) (s : type686 A) : term630 A t z s.
Proof. exact (@lem4833629 A t z s). Qed.
Lemma lem4833631 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term630 A t z s) = (term526 A s t z).
Proof. exact (eq_refl (term630 A t z s)). Qed.
Lemma lem4833632 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : term526 A s t z.
Proof. exact (EQ_MP (@lem4833631 A s t z) (@lem4833630 A t z s)). Qed.
Lemma lem4833633 {A : Type'} (s : type686 A) (t : type686 A) (z : A) (v : A -> Prop) : term631 A s t z v.
Proof. exact (@lem4833632 A s t z v). Qed.
Lemma lem4833634 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term631 A s t z v) = (term522 A v s t z).
Proof. exact (eq_refl (term631 A s t z v)). Qed.
Lemma lem4833635 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term522 A v s t z.
Proof. exact (EQ_MP (@lem4833634 A v s t z) (@lem4833633 A s t z v)). Qed.
Lemma lem4833636 {A : Type'} (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (u : A -> Prop) : term632 A v s t z u.
Proof. exact (@lem4833635 A v s t z u). Qed.
Lemma lem4833637 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : (term632 A v s t z u) = (term514 A u v s t z).
Proof. exact (eq_refl (term632 A v s t z u)). Qed.
Lemma lem4833638 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term514 A u v s t z.
Proof. exact (EQ_MP (@lem4833637 A u v s t z) (@lem4833636 A v s t z u)). Qed.
Lemma lem4833640 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term514 A u v s t z.
Proof. exact (@lem4832549 A u v s t z (@lem4833638 A u v s t z)). Qed.
Lemma lem4833641 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term515 A u v s t z) : False.
Proof. exact (@lem4833640 A u v s t z (@lem4832533 A u v s t z h1)). Qed.
Lemma lem4833642 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term515 A u v s t z) : (term515 A u v s t z) = False.
Proof. exact (prop_ext (fun h2 : term515 A u v s t z => @lem4833641 A u v s t z h1) (fun h2 : False => @lem4832533 A u v s t z h1)). Qed.
Lemma lem4833643 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) (h1 : term515 A u v s t z) : False.
Proof. exact (EQ_MP (@lem4833642 A u v s t z h1) (@lem4832533 A u v s t z h1)). Qed.
Lemma lem4833644 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term514 A u v s t z.
Proof. exact (fun h0 : term515 A u v s t z => @lem4833643 A u v s t z h0). Qed.
Lemma lem4833645 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term513 A u v s t z.
Proof. exact (EQ_MP (@lem4832532 A u v s t z) (@lem4833644 A u v s t z)). Qed.
Lemma lem4833646 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term484 A u v s t z.
Proof. exact (EQ_MP (@lem4832528 A u v s t z) (@lem4833645 A u v s t z)). Qed.
Lemma lem4833647 {A : Type'} (u : A -> Prop) (v : A -> Prop) (s : type686 A) (t : type686 A) (z : A) : term483 A u v s t z.
Proof. exact (EQ_MP (@lem4832359 A u v s t z) (@lem4833646 A u v s t z)). Qed.
Lemma lem4833648 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term395 A u v s t z.
Proof. exact (@lem4833647 A u v s t z (@lem4832286 A z u s v t h1 h2 h3 h4 h5)). Qed.
Lemma lem4833649 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term9 A u v) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term389 A u v s t z.
Proof. exact (EQ_MP (@lem4831521 A z u s v t h1 h4 h5) (@lem4833648 A z u s v t h1 h2 h3 h4 h5)). Qed.
Lemma lem4833650 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : u = v) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term389 A u v s t z.
Proof. exact (EQ_MP (@lem4831426 A z u s v t h1 h4 h5) (@lem4832272 A z u s v t h1 h2 h3 h4 h5)). Qed.
Lemma lem4833651 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : @IN A z u) (h2 : @IN A z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term389 A u v s t z.
Proof. exact (or_elim (@lem4829805 A u v) (fun h0 : u = v => @lem4833650 A z u s v t h0 h1 h2 h3 h4) (fun h0 : term9 A u v => @lem4833649 A z u s v t h0 h1 h2 h3 h4)). Qed.
Lemma lem4833652 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (@lem4833651 A z u s v t h2 h3 h4 h5 (@lem4831310 A u v s t h1)). Qed.
Lemma lem4833653 {A : Type'} (s : type686 A) (t : type686 A) (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term252 A s t u z v) : term220 A t u z v.
Proof. exact (proj2 (@lem4831298 A s t u z v h1)). Qed.
Lemma lem4833654 {A : Type'} (s : type686 A) (t : type686 A) (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term252 A s t u z v) : @IN (A -> Prop) u s.
Proof. exact (proj1 (@lem4831298 A s t u z v h1)). Qed.
Lemma lem4833655 {A : Type'} (t : type686 A) (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term220 A t u z v) : term38 A u z v.
Proof. exact (proj2 (@lem4831299 A t u z v h1)). Qed.
Lemma lem4833656 {A : Type'} (t : type686 A) (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term220 A t u z v) : @IN (A -> Prop) v t.
Proof. exact (proj1 (@lem4831299 A t u z v h1)). Qed.
Lemma lem4833657 {A : Type'} (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term38 A u z v) : @IN A z v.
Proof. exact (proj2 (@lem4831301 A u z v h1)). Qed.
Lemma lem4833658 {A : Type'} (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term38 A u z v) : @IN A z u.
Proof. exact (proj1 (@lem4831301 A u z v h1)). Qed.
Lemma lem4833659 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z v) = (term237 A s t z).
Proof. exact (prop_ext (fun h6 : @IN A z v => @lem4833652 A z u s v t h1 h2 h3 h4 h5) (fun h6 : term237 A s t z => @lem4831303 A z v h3)). Qed.
Lemma lem4833660 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833659 A z u s v t h1 h2 h3 h4 h5) (@lem4831303 A z v h3)). Qed.
Lemma lem4833661 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z u) = (term237 A s t z).
Proof. exact (prop_ext (fun h6 : @IN A z u => @lem4833660 A z u s v t h1 h2 h3 h4 h5) (fun h6 : term237 A s t z => @lem4831304 A z u h2)). Qed.
Lemma lem4833662 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : @IN A z u) (h3 : @IN A z v) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833661 A z u s v t h1 h2 h3 h4 h5) (@lem4831304 A z u h2)). Qed.
Lemma lem4833663 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : term38 A u z v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : (@IN A z v) = (term237 A s t z).
Proof. exact (prop_ext (fun h6 : @IN A z v => @lem4833662 A z u s v t h1 h3 h6 h4 h5) (fun h6 : term237 A s t z => @lem4833657 A u z v h2)). Qed.
Lemma lem4833664 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : term38 A u z v) (h3 : @IN A z u) (h4 : @IN (A -> Prop) u s) (h5 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833663 A z u s v t h1 h2 h3 h4 h5) (@lem4833657 A u z v h2)). Qed.
Lemma lem4833665 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : term38 A u z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : (@IN A z u) = (term237 A s t z).
Proof. exact (prop_ext (fun h5 : @IN A z u => @lem4833664 A z u s v t h1 h2 h5 h3 h4) (fun h5 : term237 A s t z => @lem4833658 A u z v h2)). Qed.
Lemma lem4833666 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : term38 A u z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833665 A z u s v t h1 h2 h3 h4) (@lem4833658 A u z v h2)). Qed.
Lemma lem4833667 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : term38 A u z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : (@IN (A -> Prop) v t) = (term237 A s t z).
Proof. exact (prop_ext (fun h5 : @IN (A -> Prop) v t => @lem4833666 A z u s v t h1 h2 h3 h4) (fun h5 : term237 A s t z => @lem4831302 A v t h4)). Qed.
Lemma lem4833668 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : term38 A u z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833667 A z u s v t h1 h2 h3 h4) (@lem4831302 A v t h4)). Qed.
Lemma lem4833669 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : term220 A t u z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : (term38 A u z v) = (term237 A s t z).
Proof. exact (prop_ext (fun h5 : term38 A u z v => @lem4833668 A z u s v t h1 h5 h3 h4) (fun h5 : term237 A s t z => @lem4833655 A t u z v h2)). Qed.
Lemma lem4833670 {A : Type'} (z : A) (u : A -> Prop) (s : type686 A) (v : A -> Prop) (t : type686 A) (h1 : term195 A s t) (h2 : term220 A t u z v) (h3 : @IN (A -> Prop) u s) (h4 : @IN (A -> Prop) v t) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833669 A z u s v t h1 h2 h3 h4) (@lem4833655 A t u z v h2)). Qed.
Lemma lem4833671 {A : Type'} (t : type686 A) (z : A) (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : term195 A s t) (h2 : term220 A t u z v) (h3 : @IN (A -> Prop) u s) : (@IN (A -> Prop) v t) = (term237 A s t z).
Proof. exact (prop_ext (fun h4 : @IN (A -> Prop) v t => @lem4833670 A z u s v t h1 h2 h3 h4) (fun h4 : term237 A s t z => @lem4833656 A t u z v h2)). Qed.
Lemma lem4833672 {A : Type'} (t : type686 A) (z : A) (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : term195 A s t) (h2 : term220 A t u z v) (h3 : @IN (A -> Prop) u s) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833671 A t z v u s h1 h2 h3) (@lem4833656 A t u z v h2)). Qed.
Lemma lem4833673 {A : Type'} (t : type686 A) (z : A) (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : term195 A s t) (h2 : term220 A t u z v) (h3 : @IN (A -> Prop) u s) : (@IN (A -> Prop) u s) = (term237 A s t z).
Proof. exact (prop_ext (fun h4 : @IN (A -> Prop) u s => @lem4833672 A t z v u s h1 h2 h3) (fun h4 : term237 A s t z => @lem4831300 A u s h3)). Qed.
Lemma lem4833674 {A : Type'} (t : type686 A) (z : A) (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : term195 A s t) (h2 : term220 A t u z v) (h3 : @IN (A -> Prop) u s) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833673 A t z v u s h1 h2 h3) (@lem4831300 A u s h3)). Qed.
Lemma lem4833675 {A : Type'} (t : type686 A) (z : A) (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : term195 A s t) (h2 : term252 A s t u z v) (h3 : @IN (A -> Prop) u s) : (term220 A t u z v) = (term237 A s t z).
Proof. exact (prop_ext (fun h4 : term220 A t u z v => @lem4833674 A t z v u s h1 h4 h3) (fun h4 : term237 A s t z => @lem4833653 A s t u z v h2)). Qed.
Lemma lem4833676 {A : Type'} (t : type686 A) (z : A) (v : A -> Prop) (u : A -> Prop) (s : type686 A) (h1 : term195 A s t) (h2 : term252 A s t u z v) (h3 : @IN (A -> Prop) u s) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833675 A t z v u s h1 h2 h3) (@lem4833653 A s t u z v h2)). Qed.
Lemma lem4833677 {A : Type'} (s : type686 A) (t : type686 A) (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term195 A s t) (h2 : term252 A s t u z v) : (@IN (A -> Prop) u s) = (term237 A s t z).
Proof. exact (prop_ext (fun h3 : @IN (A -> Prop) u s => @lem4833676 A t z v u s h1 h2 h3) (fun h3 : term237 A s t z => @lem4833654 A s t u z v h2)). Qed.
Lemma lem4833678 {A : Type'} (s : type686 A) (t : type686 A) (u : A -> Prop) (z : A) (v : A -> Prop) (h1 : term195 A s t) (h2 : term252 A s t u z v) : term237 A s t z.
Proof. exact (EQ_MP (@lem4833677 A s t u z v h1 h2) (@lem4833654 A s t u z v h2)). Qed.
Lemma lem4833679 {A : Type'} (u : A -> Prop) (v : A -> Prop) (z : A) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term289 A u v s t z.
Proof. exact (fun h0 : term252 A s t u z v => @lem4833678 A s t u z v h1 h0). Qed.
Lemma lem4833684 {A : Type'} (u : A -> Prop) (z : A) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term292 A u s t z.
Proof. exact (fun v : A -> Prop => @lem4833679 A u v z s t h1). Qed.
Lemma lem4833689 {A : Type'} (z : A) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term294 A s t z.
Proof. exact (fun u : A -> Prop => @lem4833684 A u z s t h1). Qed.
Lemma lem4833690 {A : Type'} (z : A) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term268 A s t z.
Proof. exact (EQ_MP (@lem4830474 A s t z) (@lem4833689 A z s t h1)). Qed.
Lemma lem4833691 {A : Type'} (z : A) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term633 A s t z.
Proof. exact (conj (@lem4833690 A z s t h1) (@lem4831297 A s t z)). Qed.
Lemma lem4833692 {A : Type'} (s : type686 A) (t : type686 A) (z : A) : (term633 A s t z) = ((term257 A s t z) = (term237 A s t z)).
Proof. exact (@lem32 (term257 A s t z) (term237 A s t z)). Qed.
Lemma lem4833693 {A : Type'} (z : A) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : (term257 A s t z) = (term237 A s t z).
Proof. exact (EQ_MP (@lem4833692 A s t z) (@lem4833691 A z s t h1)). Qed.
Lemma lem4833694 {A : Type'} (z : A) (s : type686 A) (t : type686 A) (h1 : term195 A s t) : (term225 A s t z) = (term237 A s t z).
Proof. exact (EQ_MP (@lem4830393 A s t z) (@lem4833693 A z s t h1)). Qed.
Lemma lem4833699 {A : Type'} (s : type686 A) (t : type686 A) (h1 : term195 A s t) : term240 A s t.
Proof. exact (fun z : A => @lem4833694 A z s t h1). Qed.
Lemma lem4833700 {A : Type'} (s : type686 A) (t : type686 A) : term241 A s t.
Proof. exact (fun h0 : term195 A s t => @lem4833699 A s t h0). Qed.
Lemma lem4833701 {A : Type'} (s : type686 A) (t : type686 A) : term173 A s t.
Proof. exact (EQ_MP (@lem4830334 A s t) (@lem4833700 A s t)). Qed.
Lemma lem4833702 {A : Type'} (s : type686 A) (t : type686 A) : term171 A s t.
Proof. exact (EQ_MP (@lem4830129 A s t) (@lem4833701 A s t)). Qed.
Lemma lem4833703 {A : Type'} (s : type686 A) (t : type686 A) : term170 A s t.
Proof. exact (EQ_MP (@lem4830122 A s t) (@lem4833702 A s t)). Qed.
Lemma lem4833708 {A : Type'} (s : type686 A) : term634 A s.
Proof. exact (fun t : type686 A => @lem4833703 A s t). Qed.
Lemma lem4833713 {A : Type'} : term635 A.
Proof. exact (fun s : type686 A => @lem4833708 A s). Qed.
