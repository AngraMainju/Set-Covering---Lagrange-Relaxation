#include <bits/stdc++.h>
#include <lemon/list_graph.h>
#include <lemon/lgf_reader.h>
#include <lemon/lgf_writer.h>
#include <lemon/graph_to_eps.h>
#include <lemon/time_measure.h>
#include <lemon/arg_parser.h>
#include <lemon/dijkstra.h>
#include <lemon/adaptors.h>
#include <lemon/concepts/digraph.h>
#include <lemon/concepts/path.h>
#include <lemon/connectivity.h>
#include <tuple>
#include <set>
#include <lemon/preflow.h>
#include <lemon/lp.h>

using namespace std;
using namespace lemon;

#define all(x) begin(x), end(x)
#define FOR(i, n) for (int i = 0; i < (n); ++i)

const bool DEBUG = false;
const bool DEBUG_LAGRANGE = false;

template <class C>
void Print_vector(const C &Original)
{
   for (const auto &v : Original)
   {
      cout << v << " ";
   }
   cout << endl;
}

template <class T, class C>
void Print_pair(const pair<T, C> &M, std::ostream &os = std::cout)
{
   os << "(" << M.first << " , " << M.second << " ) ";
}

template <class C>
void Print_vector_pairs(const C &Original, std::ostream &os = std::cout)
{
   for (const auto &v : Original)
   {
      Print_pair(v, os);
   }
   os << endl;
}

template <class C>
void Print_Matrix(const vector<vector<C>> &M, bool space = true)
{
   for (int i = 0; i < (int)M.size(); ++i)
   {
      for (int j = 0; j < (int)M[i].size(); ++j)
      {
         cout << M[i][j];
         if (space)
            cout << " ";
      }
      cout << endl;
   }
}

class SetCovering
{

public:
   int rows_, columns_, maxcost_;
   int max_iteration;
   double probability_of_entry_;
   vector<vector<int>> columns_charvec_;
   vector<vector<int>> rows_charvec_; //Index of 1s in the row
   vector<int> cost_vector_;

   vector<int> solution_x_;
   vector<int> inequal_indexes_;
  
   vector<double> lambda_opt_; // size: rows_
   
  
  

   SetCovering(double prob, int r, int c, int m, int max_it) : probability_of_entry_{prob}, rows_{r}, columns_{c}, maxcost_{m}, max_iteration{max_it}
   {

      //Generating Matrix
      GenerateMatrix();
      if (DEBUG)
         Print_Matrix(rows_charvec_);
      GenerateCVec();
      if (DEBUG)
      {
         cout << "COST VECTOR: ";
         Print_vector(cost_vector_);
      }

      GenInequalIndexes();
      LagrangeIPSolution(max_iteration); //to tune
      IPSolution();

      SubgradientMethod();
   }

   bool RandomDecision(double p)
   {
      std::random_device rd;  // Will be used to obtain a seed for the random number engine
      std::mt19937 gen(rd()); // Standard mersenne_twister_engine seeded with rd()

      std::discrete_distribution<> d({1 - p,
                                      p}); //std::uniform_real_distribution<> dis(0., 1.0);
      int b = d(gen);
      if (b == 1)
         return true;
      return false;
   }

   void GenerateMatrix()
   {
      int r = rows_;
      int c = columns_;
      double prob = probability_of_entry_;
      columns_charvec_.resize(c);
      rows_charvec_.resize(r);
      for (int i = 0; i < r; i++)
      {
         for (int j = 0; j < c; j++)
         {
            if (RandomDecision(prob))
            {
               rows_charvec_[i].push_back(j);
               columns_charvec_[j].push_back(i);
            }
         }
         if (rows_charvec_[i].size() == 0)
         {
            int a = std::floor(columns_ * RandomUniform01());
            rows_charvec_[i].push_back(a);
            columns_charvec_[a].push_back(i);
         }
      }

   } // GenerateMatrix

   double RandomUniform01()
   {
      std::random_device rd;  // Will be used to obtain a seed for the random number engine
      std::mt19937 gen(rd()); // Standard mersenne_twister_engine seeded with rd()
      std::uniform_real_distribution<> dis(0., 1.0);
      return dis(gen);
   }

   void GenerateCVec()
   {
      for (int i = 0; i < columns_; i++)
      {
         cost_vector_.push_back(std::floor(1 + maxcost_ * RandomUniform01()));
      }
   }
	
  	template <typename T, typename M>
   double ScalarProduct(vector<T> &a, vector<M> &b) {
      //A[i]*x = a*b
      T sumi = 0;
      for(auto &v : a) sumi += b[v];
      return sumi;
    }
  
  
   void IPSolution()
   {
      lemon::Timer t(1);
      Mip mip;
      vector<Mip::Col> x; //In or Out of solution
      FOR(i, columns_)
      {
         x.push_back(mip.addCol());
         mip.colLowerBound(x[i], 0);
         mip.colUpperBound(x[i], 1);
         mip.colType(x[i], Mip::INTEGER);
      }

      FOR(i, rows_)
      {
         Mip::Expr temp;
         FOR(j, (int)rows_charvec_[i].size())
         {
            temp += x[rows_charvec_[i][j]];
         }
         mip.addRow(temp >= 1);
      }

      Mip::Expr cost_x;
      FOR(i, columns_)
      {
         cost_x += cost_vector_[i] * x[i];
      }
      mip.min();
      mip.obj(cost_x);
      mip.solve();
      std::cout << "IP done in " << t.userTime() << "s" << std::endl;
      // Print the results
      if (mip.type() == Mip::OPTIMAL || mip.type() == Mip::FEASIBLE)
      {
         cout << "OPTIMAL MIN COST: " << mip.solValue() << endl;
         cout << "SOLUTION:\n";
         FOR(i, columns_)
         {
            cout << mip.sol(x[i]) << " ";
         }
      }
      else
      {
         std::cout << "Optimal solution not found." << std::endl;
      }
   }

   void GenInequalIndexes()
   {
      vector<bool> covered_vertices(columns_, 0);
      for (int i = 0; i < rows_; i++)
      {
         bool nonoverlapping = 1;
         for (int j = 0; j < rows_charvec_[i].size(); j++)
         {
            if (covered_vertices[rows_charvec_[i][j]])
            {
               nonoverlapping = 0;
               break;
            }
         }
         if (nonoverlapping)
         {
            inequal_indexes_.push_back(i);
            for (int j = 0; j < rows_charvec_[i].size(); j++)
            {
               covered_vertices[rows_charvec_[i][j]] = 1;
            }
         }
      }
   }
	
  
  vector<int> LagrangeIPSolutionOneStep(vector<double> &lambda_curr, bool print_out = false) {
      Mip mip;
      vector<Mip::Col> x; //In or Out of solution
      FOR(i, columns_)
      {
         x.push_back(mip.addCol());
         mip.colLowerBound(x[i], 0);
         mip.colUpperBound(x[i], 1);
         mip.colType(x[i], Mip::INTEGER);
      }
     
     Mip::Expr expr;
    for (int j=0; j<columns_; j++) 
    {
    	expr = expr + cost_vector_[j] * x[j];
    }
    
  	for (int i=0; i<rows_; i++)
    {
        expr = expr + lambda_curr[i];
        for(auto &v : rows_charvec_[i]) // sumi -= lambda[i]*x[v]; lambda * (b-Ax)
        {
          expr = expr - lambda_curr[i] * x[v];
        }
    }
    mip.min();
      mip.obj(expr);
      mip.solve();
      vector<int> solution;
      // Print the results
      if (mip.type() == Mip::OPTIMAL || mip.type() == Mip::FEASIBLE)
      {
         if(print_out) cout << "LAGRANGE OPTIMAL MIN COST: " << mip.solValue() << endl;
         if(DEBUG_LAGRANGE) cout << "LAGRANGE SOLUTION:\n";
			 FOR(i, columns_)
			 {
				solution.push_back(mip.sol(x[i]));
				if(DEBUG_LAGRANGE) cout << mip.sol(x[i]) << " ";
			 }
      }
      else
      {
         if(DEBUG_LAGRANGE || print_out) std::cout << "LAGRANGE Optimal solution not found." << std::endl;
      }
    return solution;
  }
  
   void LagrangeIPSolution(int max_iteration) {
	   lemon::Timer t(1);
     	vector<int> x_curr_opt;
		vector<double> lambda_curr;
     	FOR(i,rows_) lambda_curr.push_back(RandomUniform01());
     	FOR(i,max_iteration) {
          double a_step = 3*1./(i+1); //to tune
          x_curr_opt = LagrangeIPSolutionOneStep(lambda_curr, true);
          FOR(i,(int)lambda_curr.size()) {
            double si = ScalarProduct(rows_charvec_[i], x_curr_opt);
            lambda_curr[i] = std::max(lambda_curr[i] + a_step*(1-si), 0.);
          }
        }
     
     	solution_x_ = x_curr_opt;
     	LagrangeIPSolutionOneStep(lambda_curr, true);
     	std::cout << "LAGRANGE SUBGRADIENT done in " << t.userTime() << "s" << std::endl;
   }

   void SubgradientMethod() {}
};

int main()
{

   SetCovering Test(0.1, 100, 100, 5, 500);
   /*Print_Matrix(Test.rows_charvec_);
   Print_vector(Test.inequal_indexes_);*/

   return 0;
}
