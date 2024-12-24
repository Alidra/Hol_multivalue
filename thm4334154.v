Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4334154_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem4333784 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4333785 {A B : Type'} : ((term1 A B) = (term2 A B)) = (term3 A B).
Proof. exact (@lem4333784 ((term1 A B) = (term2 A B))). Qed.
Lemma lem4333786 {A B : Type'} : (term3 A B) = ((term1 A B) = (term2 A B)).
Proof. exact (SYM (@lem4333785 A B)). Qed.
Lemma lem4333787 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem4333790 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem4333791 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term3 A B => @lem4333790 A B h0). Qed.
Lemma lem4333792 {A B : Type'} (h1 : term5 A B) : term5 A B.
Proof. exact (h1). Qed.
Lemma lem4333793 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem4333794 {A B : Type'} (h1 : term3 A B) (h2 : term5 A B) : term3 A B.
Proof. exact (@lem4333792 A B h2 (@lem4333793 A B h1)). Qed.
Lemma lem4333795 {A B : Type'} (h1 : term3 A B) : term6 A B.
Proof. exact (fun h0 : term5 A B => @lem4333794 A B h1 h0). Qed.
Lemma lem4333796 {A B : Type'} (h1 : term5 A B) : term5 A B.
Proof. exact (h1). Qed.
Lemma lem4333797 {A B : Type'} (h1 : term3 A B) (h2 : term5 A B) : term3 A B.
Proof. exact (@lem4333795 A B h1 (@lem4333796 A B h2)). Qed.
Lemma lem4333798 {A B : Type'} (h1 : term5 A B) : term5 A B.
Proof. exact (fun h0 : term3 A B => @lem4333797 A B h0 h1). Qed.
Lemma lem4333799 {A B : Type'} : term7 A B.
Proof. exact (fun h0 : term5 A B => @lem4333798 A B h0). Qed.
Lemma lem4333802 {A B : Type'} : term5 A B.
Proof. exact (@lem4333799 A B (@lem4333791 A B)). Qed.
Lemma lem4333804 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4333805 {A B : Type'} : (term3 A B) = (term8 A B).
Proof. exact (@lem4333804 (term4 A B)). Qed.
Lemma lem4333807 (t : Prop) : (term9 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4333808 {A B : Type'} : (term8 A B) = ((term1 A B) = (term2 A B)).
Proof. exact (@lem4333807 ((term1 A B) = (term2 A B))). Qed.
Lemma lem4333837 {A B : Type'} : (term3 A B) = ((term1 A B) = (term2 A B)).
Proof. exact (TRANS (@lem4333805 A B) (@lem4333808 A B)). Qed.
Lemma lem4333838 {A B : Type'} : ((term1 A B) = (term2 A B)) = (term3 A B).
Proof. exact (SYM (@lem4333837 A B)). Qed.
Lemma lem4333840 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4333841 {A B : Type'} : ((term1 A B) = (term2 A B)) = (term3 A B).
Proof. exact (@lem4333840 ((term1 A B) = (term2 A B))). Qed.
Lemma lem4333842 {A B : Type'} : (term3 A B) = ((term1 A B) = (term2 A B)).
Proof. exact (SYM (@lem4333841 A B)). Qed.
Lemma lem4333843 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem4333852 {A B : Type'} : (term10 A B) = (term11 A B).
Proof. exact (@lem17160 (@INFINITE B (@UNIV B)) (@INFINITE A (@UNIV A))). Qed.
Lemma lem4333864 {A B : Type'} : (term12 A B) = (term13 A B).
Proof. exact (@lem17160 (@INFINITE A (@UNIV A)) (@INFINITE B (@UNIV B))). Qed.
Lemma lem4333867 {A B : Type'} : (term2 A B) = (term2 A B).
Proof. exact (eq_refl (term2 A B)). Qed.
Lemma lem4333868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4333869 {A B : Type'} : (term14 A B) = (term15 A B).
Proof. exact (MK_COMB (@lem4333868) (@lem4333852 A B)). Qed.
Lemma lem4333870 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem4333869 A B) (@lem4333867 A B)). Qed.
Lemma lem4333872 {A B : Type'} : (term18 A B) = (term18 A B).
Proof. exact (eq_refl (term18 A B)). Qed.
Lemma lem4333873 {A B : Type'} : (term19 A B) = (term20 A B).
Proof. exact (MK_COMB (@lem4333872 A B) (@lem4333864 A B)). Qed.
Lemma lem4333874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4333875 {A B : Type'} : (term21 A B) = (term22 A B).
Proof. exact (MK_COMB (@lem4333874) (@lem4333873 A B)). Qed.
Lemma lem4333876 {A B : Type'} : (term23 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem4333875 A B) (@lem4333870 A B)). Qed.
Lemma lem4333877 {A B : Type'} : (term4 A B) = (term23 A B).
Proof. exact (@lem17646 (term1 A B) (term2 A B)). Qed.
Lemma lem4333882 {A B : Type'} : (term4 A B) = (term24 A B).
Proof. exact (TRANS (@lem4333877 A B) (@lem4333876 A B)). Qed.
Lemma lem4333937 {A B : Type'} (h1 : term4 A B) : term24 A B.
Proof. exact (EQ_MP (@lem4333882 A B) (@lem4333843 A B h1)). Qed.
Lemma lem4333938 {A B : Type'} (h1 : term20 A B) : term20 A B.
Proof. exact (h1). Qed.
Lemma lem4333939 {A B : Type'} (h1 : term17 A B) : term17 A B.
Proof. exact (h1). Qed.
Lemma lem4333940 {A B : Type'} (h1 : term20 A B) : term13 A B.
Proof. exact (proj2 (@lem4333938 A B h1)). Qed.
Lemma lem4333941 {A B : Type'} (h1 : term20 A B) : term1 A B.
Proof. exact (proj1 (@lem4333938 A B h1)). Qed.
Lemma lem4333946 {A B : Type'} (h1 : term17 A B) : term2 A B.
Proof. exact (proj2 (@lem4333939 A B h1)). Qed.
Lemma lem4333947 {A B : Type'} (h1 : term17 A B) : term11 A B.
Proof. exact (proj1 (@lem4333939 A B h1)). Qed.
Lemma lem4333963 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : @INFINITE B (@UNIV B).
Proof. exact (h1). Qed.
Lemma lem4333975 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : @INFINITE A (@UNIV A).
Proof. exact (h1). Qed.
Lemma lem4333987 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : @INFINITE A (@UNIV A).
Proof. exact (h1). Qed.
Lemma lem4333999 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : @INFINITE B (@UNIV B).
Proof. exact (h1). Qed.
Lemma lem4334003 {A B : Type'} (h1 : term20 A B) : term25 B.
Proof. exact (proj2 (@lem4333940 A B h1)). Qed.
Lemma lem4334005 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : @INFINITE B (@UNIV B).
Proof. exact (h1). Qed.
Lemma lem4334007 {A B : Type'} (h1 : term20 A B) : term25 A.
Proof. exact (proj1 (@lem4333940 A B h1)). Qed.
Lemma lem4334011 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : @INFINITE A (@UNIV A).
Proof. exact (h1). Qed.
Lemma lem4334015 {A B : Type'} (h1 : term17 A B) : term25 A.
Proof. exact (proj2 (@lem4333947 A B h1)). Qed.
Lemma lem4334017 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : @INFINITE A (@UNIV A).
Proof. exact (h1). Qed.
Lemma lem4334019 {A B : Type'} (h1 : term17 A B) : term25 B.
Proof. exact (proj1 (@lem4333947 A B h1)). Qed.
Lemma lem4334023 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : @INFINITE B (@UNIV B).
Proof. exact (h1). Qed.
Lemma lem4334025 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : @INFINITE B (@UNIV B).
Proof. exact (h1). Qed.
Lemma lem4334026 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : term26 B.
Proof. exact (fun h0 : term25 B => @lem4334025 B h1). Qed.
Lemma lem4334028 (p : Prop) : (term27 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4334029 {B : Type'} : (term26 B) = (@INFINITE B (@UNIV B)).
Proof. exact (@lem4334028 (@INFINITE B (@UNIV B))). Qed.
Lemma lem4334030 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : @INFINITE B (@UNIV B).
Proof. exact (EQ_MP (@lem4334029 B) (@lem4334026 B h1)). Qed.
Lemma lem4334033 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4334035 {B : Type'} : (term25 B) = (term28 B).
Proof. exact (@lem4334033 (@INFINITE B (@UNIV B))). Qed.
Lemma lem4334038 {A B : Type'} (h1 : term20 A B) : term28 B.
Proof. exact (EQ_MP (@lem4334035 B) (@lem4334003 A B h1)). Qed.
Lemma lem4334041 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : False.
Proof. exact (@lem4334038 A B h2 (@lem4334030 B h1)). Qed.
Lemma lem4334042 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : term29.
Proof. exact (fun h0 : ~ False => @lem4334041 A B h1 h2). Qed.
Lemma lem4334044 (p : Prop) : (term27 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4334045 : term29 = False.
Proof. exact (@lem4334044 False). Qed.
Lemma lem4334046 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : False.
Proof. exact (EQ_MP (@lem4334045) (@lem4334042 A B h1 h2)). Qed.
Lemma lem4334048 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : @INFINITE A (@UNIV A).
Proof. exact (h1). Qed.
Lemma lem4334049 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : term26 A.
Proof. exact (fun h0 : term25 A => @lem4334048 A h1). Qed.
Lemma lem4334051 (p : Prop) : (term27 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4334052 {A : Type'} : (term26 A) = (@INFINITE A (@UNIV A)).
Proof. exact (@lem4334051 (@INFINITE A (@UNIV A))). Qed.
Lemma lem4334053 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : @INFINITE A (@UNIV A).
Proof. exact (EQ_MP (@lem4334052 A) (@lem4334049 A h1)). Qed.
Lemma lem4334056 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4334058 {A : Type'} : (term25 A) = (term28 A).
Proof. exact (@lem4334056 (@INFINITE A (@UNIV A))). Qed.
Lemma lem4334061 {A B : Type'} (h1 : term20 A B) : term28 A.
Proof. exact (EQ_MP (@lem4334058 A) (@lem4334007 A B h1)). Qed.
Lemma lem4334064 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : False.
Proof. exact (@lem4334061 A B h2 (@lem4334053 A h1)). Qed.
Lemma lem4334065 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : term29.
Proof. exact (fun h0 : ~ False => @lem4334064 A B h1 h2). Qed.
Lemma lem4334067 (p : Prop) : (term27 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4334068 : term29 = False.
Proof. exact (@lem4334067 False). Qed.
Lemma lem4334069 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : False.
Proof. exact (EQ_MP (@lem4334068) (@lem4334065 A B h1 h2)). Qed.
Lemma lem4334071 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : @INFINITE A (@UNIV A).
Proof. exact (h1). Qed.
Lemma lem4334072 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : term26 A.
Proof. exact (fun h0 : term25 A => @lem4334071 A h1). Qed.
Lemma lem4334074 (p : Prop) : (term27 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4334075 {A : Type'} : (term26 A) = (@INFINITE A (@UNIV A)).
Proof. exact (@lem4334074 (@INFINITE A (@UNIV A))). Qed.
Lemma lem4334076 {A : Type'} (h1 : @INFINITE A (@UNIV A)) : @INFINITE A (@UNIV A).
Proof. exact (EQ_MP (@lem4334075 A) (@lem4334072 A h1)). Qed.
Lemma lem4334079 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4334081 {A : Type'} : (term25 A) = (term28 A).
Proof. exact (@lem4334079 (@INFINITE A (@UNIV A))). Qed.
Lemma lem4334084 {A B : Type'} (h1 : term17 A B) : term28 A.
Proof. exact (EQ_MP (@lem4334081 A) (@lem4334015 A B h1)). Qed.
Lemma lem4334087 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : False.
Proof. exact (@lem4334084 A B h2 (@lem4334076 A h1)). Qed.
Lemma lem4334088 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : term29.
Proof. exact (fun h0 : ~ False => @lem4334087 A B h1 h2). Qed.
Lemma lem4334090 (p : Prop) : (term27 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4334091 : term29 = False.
Proof. exact (@lem4334090 False). Qed.
Lemma lem4334092 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : False.
Proof. exact (EQ_MP (@lem4334091) (@lem4334088 A B h1 h2)). Qed.
Lemma lem4334094 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : @INFINITE B (@UNIV B).
Proof. exact (h1). Qed.
Lemma lem4334095 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : term26 B.
Proof. exact (fun h0 : term25 B => @lem4334094 B h1). Qed.
Lemma lem4334097 (p : Prop) : (term27 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4334098 {B : Type'} : (term26 B) = (@INFINITE B (@UNIV B)).
Proof. exact (@lem4334097 (@INFINITE B (@UNIV B))). Qed.
Lemma lem4334099 {B : Type'} (h1 : @INFINITE B (@UNIV B)) : @INFINITE B (@UNIV B).
Proof. exact (EQ_MP (@lem4334098 B) (@lem4334095 B h1)). Qed.
Lemma lem4334102 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4334104 {B : Type'} : (term25 B) = (term28 B).
Proof. exact (@lem4334102 (@INFINITE B (@UNIV B))). Qed.
Lemma lem4334107 {A B : Type'} (h1 : term17 A B) : term28 B.
Proof. exact (EQ_MP (@lem4334104 B) (@lem4334019 A B h1)). Qed.
Lemma lem4334110 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : False.
Proof. exact (@lem4334107 A B h2 (@lem4334099 B h1)). Qed.
Lemma lem4334111 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : term29.
Proof. exact (fun h0 : ~ False => @lem4334110 A B h1 h2). Qed.
Lemma lem4334113 (p : Prop) : (term27 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4334114 : term29 = False.
Proof. exact (@lem4334113 False). Qed.
Lemma lem4334115 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : False.
Proof. exact (EQ_MP (@lem4334114) (@lem4334111 A B h1 h2)). Qed.
Lemma lem4334116 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : (@INFINITE B (@UNIV B)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE B (@UNIV B) => @lem4334115 A B h1 h2) (fun h3 : False => @lem4334023 B h1)). Qed.
Lemma lem4334117 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : False.
Proof. exact (EQ_MP (@lem4334116 A B h1 h2) (@lem4334023 B h1)). Qed.
Lemma lem4334118 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : (@INFINITE A (@UNIV A)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE A (@UNIV A) => @lem4334092 A B h1 h2) (fun h3 : False => @lem4334017 A h1)). Qed.
Lemma lem4334119 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : False.
Proof. exact (EQ_MP (@lem4334118 A B h1 h2) (@lem4334017 A h1)). Qed.
Lemma lem4334120 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : (@INFINITE A (@UNIV A)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE A (@UNIV A) => @lem4334069 A B h1 h2) (fun h3 : False => @lem4334011 A h1)). Qed.
Lemma lem4334121 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : False.
Proof. exact (EQ_MP (@lem4334120 A B h1 h2) (@lem4334011 A h1)). Qed.
Lemma lem4334122 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : (@INFINITE B (@UNIV B)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE B (@UNIV B) => @lem4334046 A B h1 h2) (fun h3 : False => @lem4334005 B h1)). Qed.
Lemma lem4334123 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : False.
Proof. exact (EQ_MP (@lem4334122 A B h1 h2) (@lem4334005 B h1)). Qed.
Lemma lem4334124 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : (@INFINITE B (@UNIV B)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE B (@UNIV B) => @lem4334117 A B h1 h2) (fun h3 : False => @lem4333999 B h1)). Qed.
Lemma lem4334125 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : False.
Proof. exact (EQ_MP (@lem4334124 A B h1 h2) (@lem4333999 B h1)). Qed.
Lemma lem4334126 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : (@INFINITE A (@UNIV A)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE A (@UNIV A) => @lem4334119 A B h1 h2) (fun h3 : False => @lem4333987 A h1)). Qed.
Lemma lem4334127 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : False.
Proof. exact (EQ_MP (@lem4334126 A B h1 h2) (@lem4333987 A h1)). Qed.
Lemma lem4334128 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : (@INFINITE A (@UNIV A)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE A (@UNIV A) => @lem4334121 A B h1 h2) (fun h3 : False => @lem4333975 A h1)). Qed.
Lemma lem4334129 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : False.
Proof. exact (EQ_MP (@lem4334128 A B h1 h2) (@lem4333975 A h1)). Qed.
Lemma lem4334130 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : (@INFINITE B (@UNIV B)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE B (@UNIV B) => @lem4334123 A B h1 h2) (fun h3 : False => @lem4333963 B h1)). Qed.
Lemma lem4334131 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : False.
Proof. exact (EQ_MP (@lem4334130 A B h1 h2) (@lem4333963 B h1)). Qed.
Lemma lem4334132 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : (@INFINITE B (@UNIV B)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE B (@UNIV B) => @lem4334125 A B h1 h2) (fun h3 : False => @lem4333999 B h1)). Qed.
Lemma lem4334133 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term17 A B) : False.
Proof. exact (EQ_MP (@lem4334132 A B h1 h2) (@lem4333999 B h1)). Qed.
Lemma lem4334134 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : (@INFINITE A (@UNIV A)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE A (@UNIV A) => @lem4334127 A B h1 h2) (fun h3 : False => @lem4333987 A h1)). Qed.
Lemma lem4334135 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term17 A B) : False.
Proof. exact (EQ_MP (@lem4334134 A B h1 h2) (@lem4333987 A h1)). Qed.
Lemma lem4334136 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : (@INFINITE A (@UNIV A)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE A (@UNIV A) => @lem4334129 A B h1 h2) (fun h3 : False => @lem4333975 A h1)). Qed.
Lemma lem4334137 {A B : Type'} (h1 : @INFINITE A (@UNIV A)) (h2 : term20 A B) : False.
Proof. exact (EQ_MP (@lem4334136 A B h1 h2) (@lem4333975 A h1)). Qed.
Lemma lem4334138 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : (@INFINITE B (@UNIV B)) = False.
Proof. exact (prop_ext (fun h3 : @INFINITE B (@UNIV B) => @lem4334131 A B h1 h2) (fun h3 : False => @lem4333963 B h1)). Qed.
Lemma lem4334139 {A B : Type'} (h1 : @INFINITE B (@UNIV B)) (h2 : term20 A B) : False.
Proof. exact (EQ_MP (@lem4334138 A B h1 h2) (@lem4333963 B h1)). Qed.
Lemma lem4334140 {A B : Type'} (h1 : term17 A B) : False.
Proof. exact (or_elim (@lem4333946 A B h1) (fun h0 : @INFINITE A (@UNIV A) => @lem4334135 A B h0 h1) (fun h0 : @INFINITE B (@UNIV B) => @lem4334133 A B h0 h1)). Qed.
Lemma lem4334141 {A B : Type'} (h1 : term20 A B) : False.
Proof. exact (or_elim (@lem4333941 A B h1) (fun h0 : @INFINITE B (@UNIV B) => @lem4334139 A B h0 h1) (fun h0 : @INFINITE A (@UNIV A) => @lem4334137 A B h0 h1)). Qed.
Lemma lem4334142 {A B : Type'} (h1 : term4 A B) : False.
Proof. exact (or_elim (@lem4333937 A B h1) (fun h0 : term20 A B => @lem4334141 A B h0) (fun h0 : term17 A B => @lem4334140 A B h0)). Qed.
Lemma lem4334143 {A B : Type'} (h1 : term4 A B) : (term4 A B) = False.
Proof. exact (prop_ext (fun h2 : term4 A B => @lem4334142 A B h1) (fun h2 : False => @lem4333843 A B h1)). Qed.
Lemma lem4334144 {A B : Type'} (h1 : term4 A B) : False.
Proof. exact (EQ_MP (@lem4334143 A B h1) (@lem4333843 A B h1)). Qed.
Lemma lem4334145 {A B : Type'} : term3 A B.
Proof. exact (fun h0 : term4 A B => @lem4334144 A B h0). Qed.
Lemma lem4334146 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (EQ_MP (@lem4333842 A B) (@lem4334145 A B)). Qed.
Lemma lem4334147 {A B : Type'} : term3 A B.
Proof. exact (EQ_MP (@lem4333838 A B) (@lem4334146 A B)). Qed.
Lemma lem4334149 {A B : Type'} : term3 A B.
Proof. exact (@lem4333802 A B (@lem4334147 A B)). Qed.
Lemma lem4334150 {A B : Type'} (h1 : term4 A B) : False.
Proof. exact (@lem4334149 A B (@lem4333787 A B h1)). Qed.
Lemma lem4334151 {A B : Type'} (h1 : term4 A B) : (term4 A B) = False.
Proof. exact (prop_ext (fun h2 : term4 A B => @lem4334150 A B h1) (fun h2 : False => @lem4333787 A B h1)). Qed.
Lemma lem4334152 {A B : Type'} (h1 : term4 A B) : False.
Proof. exact (EQ_MP (@lem4334151 A B h1) (@lem4333787 A B h1)). Qed.
Lemma lem4334153 {A B : Type'} : term3 A B.
Proof. exact (fun h0 : term4 A B => @lem4334152 A B h0). Qed.
Lemma lem4334154 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (EQ_MP (@lem4333786 A B) (@lem4334153 A B)). Qed.
