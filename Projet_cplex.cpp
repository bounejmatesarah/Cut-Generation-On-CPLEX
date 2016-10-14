

#include <iostream>
#include <ilcplex/ilocplex.h>

using namespace std;



struct Graph {
 int vertexCount;
 int edgeCount;
 int** adjacencyMatrix;

 Graph(int vertexCount) {
   this->vertexCount = vertexCount;
   this->edgeCount = 0;
   adjacencyMatrix = new int*[vertexCount];
   for (int i = 0; i < vertexCount; i++) {
     adjacencyMatrix[i] = new int[vertexCount];
     for (int j = 0; j < vertexCount; j++)
       adjacencyMatrix[i][j] = -1;
   }
 }

 void addEdge(int i, int j) {
   if (i >= 0 && i < vertexCount && j >= 0 && j < vertexCount) {
     int edgeN = edgeCount++;
     adjacencyMatrix[i][j] = edgeN;
     adjacencyMatrix[j][i] = edgeN;
   }
 }

 void removeEdge(int i, int j) {
   if (i >= 0 && i < vertexCount && j >= 0 && j < vertexCount) {
     adjacencyMatrix[i][j] = -1;
     adjacencyMatrix[j][i] = -1;
   }
 }

 bool isEdge(int i, int j) {
   if (i >= 0 && i < vertexCount && j >= 0 && j < vertexCount)

     return adjacencyMatrix[i][j] != -1;
   else
     return false;
 }

 int getEdge(int i, int j) {
   if (i >= 0 && i < vertexCount && j >= 0 && j < vertexCount)
     return adjacencyMatrix[i][j];
   else
     return -1;
 }

 ~Graph() {
   for (int i = 0; i < vertexCount; i++)
     delete[] adjacencyMatrix[i];
   delete[] adjacencyMatrix;
 }
};

int C;



ILOUSERCUTCALLBACK4(CtCallback, IloArray <IloIntVarArray>, x, Graph&, graph, IloNum, eps,IloExpr, obj) {


IloExpr cutExpr(getEnv());

try {



  double cutExprValue = getValue(obj);

  if (cutExprValue < 14 - eps) {

    cout << "Cut is violated. cutExprValue = " << cutExprValue << endl;



    IloConstraint cut = (cutExpr >= 14);

    add(cut);

    cutExpr.end();

    cut.end();



  }





} catch (IloException &e) {

  cout << "Error" << endl;

  e.print(cout);

  cutExpr.end();

  throw;

}
}




ILOUSERCUTCALLBACK3(CtCallback2, IloArray <IloIntVarArray>, x, Graph&, graph, IloNum, eps) {



IloExpr cutExpr2(getEnv());

try {


  for (IloInt j = 0; j < 15; j++) {

    for (IloInt i = 0; i < 15; i++) {

      if (graph.isEdge(i,j)) {

        cutExpr2 += x[i][j];

      }

    }

  }

  float cutExprValue = getValue(cutExpr2);

  if (cutExprValue < 28/C - eps) {

    cout << "Cut is violated. cutExprValue = " << cutExprValue << endl;



    IloConstraint cut = (cutExpr2 >= 28/C );

    add(cut);

    cutExpr2.end();

    cut.end();



  }





} catch (IloException &e) {

  cout << "Error" << endl;

  e.print(cout);

  cutExpr2.end();

  throw;

}

}






int solution(Graph & G){
 IloEnv env;

   IloCplex cplex;

   IloModel model;

   try {

     env = IloEnv();

     model = IloModel(env);

     cplex = IloCplex(model);




     // Variable x[i][j] : Nombre de cables entre i et j

     IloArray < IloIntVarArray > x (env, 15);

     for (IloInt i = 0; i < 15; i++) {
    	 //faire passer du flot
       x[i] = IloIntVarArray(env, 15);

       for (IloInt j = 0; j < 15; j++) {
         x[i][j] = IloIntVar(env);


       // Ajouter une condition pour dire qu'on ne peut pas creer des cables entre
       // i et j si l'arc (i,j) n'existe pas
       if(!G.isEdge(i,j)){
       IloRange constraint = (x[i][j]<=0);
         model.add(constraint);

             }
       }
     }


     // Variable y[i][j][k] : Flot venant de k et passant entre i et j
     IloArray<IloArray<IloIntVarArray> > y(env, 15);

     for (IloInt i = 0; i < 15; i++) {
       y[i] = IloArray<IloIntVarArray>(env, 15);

       for (IloInt j = 0; j < 15; j++) {
         y[i][j] = IloIntVarArray(env, 15);

         for (IloInt k = 0; k < 15; k++) {

           y[i][j][k] = IloIntVar(env);

           // Ajouter une condition pour dire qu'on ne peut pas faire passer du flot entre
           // i et j si l'arc (i,j) n'existe pas

           if(!G.isEdge(i,j))

           {
           IloRange constraint = (y[i][j][k]<=0);
           model.add(constraint);
                     }
         }
       }
     }




     //Premiere contrainte :
     for (IloInt k = 0; k < 15; k++) {
       IloExpr Sommesurj1(env);
       for (int j = 0; j < 15 ; j++) {


         if(G.isEdge(k,j)){
         Sommesurj1 += y[k][j][k];
         }

       }
       IloExpr Sommesurj2(env);
       for (int j = 0; j < 15 ; j++) {

         if(G.isEdge(j,k)){
         Sommesurj2 += y[j][k][k];
         }
       }
       IloRange constraint = ((Sommesurj1 - Sommesurj2) == 14);
       model.add(constraint);
       Sommesurj1.end();
       Sommesurj2.end();
     }

     //Deuxieme contrainte:
     for (IloInt i = 0; i < 15; i++) {
       for (IloInt k = 0; k < 15; k++) {
         if (i != k) {
           IloExpr Sommesurj1(env);
           for (int j = 0; j < 15; j++) {

             if(G.isEdge(i,j)){
             Sommesurj1 += y[i][j][k];
             }
           }
           IloExpr Sommesurj2(env);
           for (int j = 0; j < 15; j++) {

             if(G.isEdge(j,i))
             {
             Sommesurj2 += y[j][i][k];
             }
           }
           IloRange constraint = ((Sommesurj1 - Sommesurj2) == -1);
           model.add(constraint);
           Sommesurj1.end();
           Sommesurj2.end();
         }
       }
     }

     IloExpr somme(env);
     // Troisieme contrainte:
     IloExpr MmbrGauche (env);
     for (IloInt i = 0; i < 15; i++) {
       for (IloInt j = 0; j < 15; j++) {
    	 IloExpr somme(env);
         for (int k = 0; k < 15; k++) {

           if(G.isEdge(i,j) && G.isEdge(j,i))
           {
           somme += (y[i][j][k] + y[j][i][k]);
           MmbrGauche= somme - C * x[i][j];
           }

           IloRange constraint = (MmbrGauche <= 0);
           model.add(constraint);

         }
         somme.end();
       }
     }


     //cplex.exportModel("/net/cremi/pbyebli/prob.lp");
     // Fonction Objectif:

     IloExpr obj(env);
     for (IloInt i =0; i<15; i++) {
       for (IloInt j=i+1; j<15; j++) {

         obj += x[i][j];
       }
     }
     model.add(IloMinimize(env, obj));


     cplex.use(CtCallback(env, x, G, cplex.getParam(IloCplex::EpRHS),obj));
     cplex.use(CtCallback2(env, x, G, cplex.getParam(IloCplex::EpRHS)));

     cplex.solve();

     cerr <<"l'optimimum est : "<< cplex.getObjValue() << endl;


   } catch (IloException& e) {
     e.print(cout);
   }

   return cplex.getObjValue();
}


int main() {


    cout << "Veuillez saisir une valeur de C : " << endl;
    cin >> C;


 Graph graphe=Graph(15);
 graphe.addEdge(0,7);
//  graphe.addEdge(7,0);
 graphe.addEdge(0,6);
//  graphe.addEdge(6,0);
 graphe.addEdge(0,5);
//  graphe.addEdge(5,0);
 graphe.addEdge(1,2);
//  graphe.addEdge(2,1);
 graphe.addEdge(1,5);
//  graphe.addEdge(5,1);
 graphe.addEdge(1,4);
//  graphe.addEdge(4,1);
 graphe.addEdge(2,7);
//  graphe.addEdge(7,2);
 graphe.addEdge(2,4);
//  graphe.addEdge(4,2);
 graphe.addEdge(3,5);
//  graphe.addEdge(5,3);
 graphe.addEdge(3,4);
//  graphe.addEdge(4,3);
 graphe.addEdge(12,13);
//  graphe.addEdge(13,12);
 graphe.addEdge(12,10);
//  graphe.addEdge(10,12);
 graphe.addEdge(6,9);
//  graphe.addEdge(9,6);
 graphe.addEdge(6,13);
//  graphe.addEdge(13,6);
 graphe.addEdge(9,11);
//  graphe.addEdge(11,9);
 graphe.addEdge(9,8);
//  graphe.addEdge(8,9);
 graphe.addEdge(8,14);
//  graphe.addEdge(14,8);
 graphe.addEdge(8,7);
//  graphe.addEdge(7,8);
 graphe.addEdge(7,14);
//  graphe.addEdge(14,7);
 graphe.addEdge(5,12);
//  graphe.addEdge(12,5);

 /**********Appel de notre fonction que retourne l'optimum *********/


 solution(graphe);

 return 0;

}
