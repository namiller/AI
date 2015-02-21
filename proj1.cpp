// Nolan Miller ID:5339012800 2/1/2015 
// USC CSCI360 Project 1 A* search.

// This reeally does not represent my design asthetic as I would have
// strongly prefered to make most of these templated functions
// to operate over any generic state representation. Alas.

#include <queue>
#include <map>
#include <vector>
#include <algorithm>
#include <string>
#include <iostream>
#include <fstream>
#include <cmath>
#include "problem.h"

using namespace std;

/// you can add whatever helper functions/variables you need here.

// I really would prefer doing a lot of this stuff in a separate file and linking
// but that doesn't seem compatible with grading scheme.

/* GENERIC SPACE SAVING FUNCTIONS. ACTUALLY GOES IN PROJ1.CPP */

// I got tired of typing it.
typedef pair<int, int> point;
struct State {
    point pos;
    set<point> goals_remaining;
};
typedef float(*heur_func)(const State &s);

// ~~ used by cardinalize
const string directions[4] = {"North", "East", "South", "West"};
vector<string> cardinalize(vector<point> &path){
    vector<string> spath;
    for(int i = 1; i < path.size();i++){
        int dx = path[i].first - path[i-1].first;
        int dy = path[i].second - path[i-1].second;
        //assert(dx*dy == 0 && dx*dx+dy*dy == 1)
        spath.push_back(directions[(dx!=0)*(1+dx) + (dy!=0)*(2-dy)]);
    }
    return spath;
}

/* NODE IMPLEMENTATION. ACTUALLY GOES IN NODE.CPP */

class Node {
    public:
    State state;
    Node *parent;
    int g;
    float h;
    float f;
    Node(heur_func, const point& pos, vector<point> goals);
    Node(const point &, heur_func, Node *);
    vector<point> stateChain();
    vector<Node *> expand(heur_func, Problem &);
};

// Used for constructing the root node.
Node::Node(heur_func heuristic, const point& loc, vector<point> goals){
    this->state.pos = loc;
    this->state.goals_remaining = set<point>(goals.begin(),goals.end());
    this->state.goals_remaining.erase(loc);
    this->g = 0;
    this->h = (*heuristic)(this->state);
    this->f = this->g + this->h;
    this->parent = NULL;
}

// Used for constructing new nodes by expand.
Node::Node(const point &loc, heur_func heuristic, Node *p) {
    this->state.pos = loc;
    this->state.goals_remaining = p->state.goals_remaining;
    this->state.goals_remaining.erase(loc);
    this->g = p->g + 1;
    this->h = (*heuristic)(this->state);
    this->f = this->g + this->h;
    this->parent = p;
}

vector<Node *> Node::expand(heur_func heuristic, Problem &p) {
    vector<point> states;
        states = p.getSuccessors(this->state.pos);
    vector<Node *> ret;
    for(int i = 0; i < states.size(); i++){
        Node *exp = new Node(states[i],heuristic, this);
        ret.push_back(exp);
    }
    return ret;
}

vector<point> Node::stateChain(){
    vector<point> path;
    Node *n = this;
    while(n!=NULL){
        path.push_back(n->state.pos);
        n = n->parent;
    }
    reverse(path.begin(),path.end());
    return path;
}

struct NodePStateCompare {
    bool operator()(Node * n1, Node *n2) {
        if (n1->state.goals_remaining == n2->state.goals_remaining)
            return n1->state.pos < n2->state.pos;
        return n1->state.goals_remaining < n2->state.goals_remaining;
    }
};

struct NodePFvalCompare{
    bool operator() (Node *a, Node *b){
        // Largest g tie breaker since it will hopefully be closer to the goal.
        if (a->f == b->f) {
            return a->g < b->g; 
        }
        return a->f > b->f;
    }
};

/* A* IMPLEMENTATION. ACTUALLY GOES IN ASTAR.CPP */

// We are going to diverge slightly from traditional A* and enforce that 
// a state has a h value of 0 iff it is the goal state. This simplifies things considerably
// and allows the single goal implementation to be identical to a mutli-goal implementation
// it is provably equivalent in performance and 0+eps may be used to signify a zero valued
// non goal state.
vector<point> runAstar(Problem &problem, heur_func heuristic, vector<point> goals) {
    // Set over states not nodes (No duplicate states are inserted).
    // Only the minimum heuristic expansion of a state is inserted.
    set<Node *,NodePStateCompare> expanded;
    // Here we want the expansion queue sorted by the F value of the Node.
    priority_queue<Node *, vector<Node *>, NodePFvalCompare> expansion_queue;
    expansion_queue.push(new Node(heuristic, problem.getStartState(),goals));
    vector<point> path;
    while(!expansion_queue.empty()){
        Node *n = expansion_queue.top();
        if (n->h == 0){
            path = n->stateChain();
            break;
        } else {
            expansion_queue.pop();
            //state already expanded. Clean up memory now.
            if (expanded.find(n) != expanded.end()) {
                delete n;
            } else {
                vector<Node *> exp = n->expand(heuristic, problem);
                for (int i = 0; i < exp.size(); i++){
                    expansion_queue.push(exp[i]);
                }
                expanded.insert(n);
            }
        }
    }
    // Clean up the queue.
    while(!expansion_queue.empty()){
        delete expansion_queue.top();
        expansion_queue.pop();
    }
    // Clean up the expanded set
    for (set<Node *>::iterator it = expanded.begin(); it != expanded.end(); it++){
        delete *it;
    }
    return path;
}

/* HEURISTIC FUNCTIONS + SUPPORT. ACTUALLY GOES IN HEURISTICS.CPP */

// The rectilinear distance between two points
float manhattan(const point& s1,const point& s2){
    return fabs((float)s1.first - s2.first) + fabs((float)s1.second - s2.second);
}

// The euclidean distance between two points
float dist(const point& s1,const point& s2){
    return sqrt(pow((float)s1.first - s2.first, 2) + pow((float)s1.second - s2.second, 2));
}

// RMST implementation //
// This is an implementation of the (planar) rectilinear minimum spanning tree
// For all possible goal states this is equivalent to the minimum spanning tree
// however it allows us to optimize the algorithm. It could be implemented in
// O(nlog(n)) however this implementation is optimizing for code complexity rather than
// time complexity and is O(n^3) in time and O(n^2) in space. (n = number of goals).
// To mitigate the relatively slow run time and the redundancy with which certain states
// are querried we will memoize goal distributions to speed up the subsequent calls.
static map<set<point>, float> mst_memo;

// Computer the sum of all elements of v.
int sumVect(vector<int> & v){
    int s =0;
    for(int i = 0; i<v.size();i++){
        s+= v[i];
    }
    return s;
}

// Calculate whether or not the given adjacency matrix is fully connected or not.
// A edge weight of zero is considered unconnected, any other value (even <0)
// is considered connected. This simplifies our in/out set.
bool fullyConnected(vector<vector<float> > &graph){
    vector<int> reached(graph.size(),0);
    reached[0] = 1;
    int sum = 1, lastSum = 0;
    while(sum!=lastSum){
        lastSum = sum;
        for(int i = 0;i < reached.size();i++){
            if(reached[i]){
                for(int ii = i+1;ii < graph.size();ii++){
                    reached[ii] |= (graph[i][ii] != 0);
                }
            }
        }
        sum = sumVect(reached);
    }
    return sumVect(reached) == reached.size();
}

// Sets the edge of the graph defined as between point.first and point.second
// to the value given and returns the overwritten value.
float setEdge(vector<vector<float> > &graph, point &p, float nv) {
    float r = graph[p.first][p.second];
    graph[p.first][p.second] = graph[p.second][p.first] = nv;
    return r;
}

// Find the maximum weight edge in the graph (must be greater than 0).
// If the max weight edge is less than 0 {-1,-1} is returned.
point findMax(vector<vector<float> > &graph){
    float max = 0;
    point ret(-1,-1);
    for(int x = 0;x < graph.size(); x++){
        for(int y = 0; y < graph.size(); y++){
            if(graph[x][y]>max){
                max = graph[x][y];
                ret.first = x;
                ret.second = y;
            }
        }
    }
    return ret;
}

// Calculate the total mass of the minimum spanning tree that connects all points
// in the set points.
float min_span_tree_manhattan(const set<point>& points){
    if(points.size() <=1)
        return 0;
    if(points.size() ==2) {
        set<point>::iterator it = points.begin();
        it++;
        return manhattan(*points.begin(),*it);
    }
    if (mst_memo.count(points))
        return mst_memo[points];
    vector<point> mapping;
    for(set<point>::iterator it = points.begin(); it != points.end();it++){
        mapping.push_back(*it);
    }
    vector<vector<float> > graph_lut(mapping.size());
    for(int i = 0;i < mapping.size();i++){
        vector<float> glist(mapping.size());
        for(int ii = 0;ii <mapping.size();ii++){
            glist[ii] = manhattan(mapping[i],mapping[ii]);
        }
        graph_lut[i] = glist;
    }
    point done(-1,-1),edge;
    while( (edge = findMax(graph_lut)) != done){
        float tmp = setEdge(graph_lut, edge, 0);
        if (!fullyConnected(graph_lut)){
            setEdge(graph_lut,edge, -1*tmp);
        }
    }
    float cost = 0;
    for(int i = 0;i < graph_lut.size();i++){
        for(int ii = i+1; ii< graph_lut.size();ii++){
            cost += graph_lut[i][ii];
        }
    }
    cost *= -1;
    mst_memo[points] = cost;
    return cost;
}

// Calculate the point in the set points with the least rectilinear distance
// to point p0.
float nearest_manhattan(const set<point>& points, const point &p0) {
    if (points.empty()){
        return 0;
    }
    float m = 999999999999;
    for(set<point>::iterator it = points.begin(); it != points.end();it++){
        m = min((float)m,manhattan(*it, p0));
    }
    return m;
}

// Calculate the point in the set points with the least euclidian distance
// to point p0.
float nearest_flight(const set<point>& points, const point &p0) {
    if (points.empty()){
        return 0;
    }
    float m = 99999999999;
    for(set<point>::iterator it = points.begin(); it != points.end();it++){
        m = min((float)m,dist(*it, p0));
    }
    return m;
}

// Calculate the sum(euclidean(p1,p0)) where p1 is an element of points.
// This alone is a terrible heuristic because it prefers p0 to be centered.
float sum_flight(const set<point>& points, const point& p0){
    float r = 0;
    for(set<point>::iterator it = points.begin(); it != points.end();it++){
        r += dist(*it, p0);
    }
    return r;
}

// Calculates the total flight distance between the center of mass and
// all points in the set. Should work for the same cases rect_group_dist works.
// hard to prove this one (and in general it does not work).
float spoke_mass(const set<point>& points){
    point center(0,0);
    for(set<point>::iterator it = points.begin(); it != points.end();it++){
        center.first += (*it).first;
        center.second += (*it).second;
    }
    center.first /= points.size();
    center.second /= points.size();
    return sum_flight(points,center);
}

// Returns the minimum manhattan path connecting the set of points that can
// describe the vertexes of a rectangle (ie at most 4 points with 2 pairs at same
// x and y val as eachother). Has different boundary case behavior than rmst.
float rect_group_dist(const set<point>& points){
    float d = 0;
    //find the two points with largest separating distance.
    if(points.size() < 2)
        return 0;
    point p1,p2;
    for(set<point>::iterator it = points.begin(); it != points.end();it++){
        for(set<point>::iterator it2 = it; it2 != points.end();it2++){
            if(manhattan(*it,*it2) > d) {
                d = manhattan(*it,*it2);
                p1 = *it;
                p2 = *it2;
            }
        }
    }
    if (points.size() == 2)
        return d;
    if (points.size() == 3){
        //farthest points must be on diagonal - d must pass between them through other point.
        return d;
    }
    set<point> pc(points);
    pc.erase(p1);
    return d + nearest_manhattan(pc,p1);
}

/* 
 These are the implementations of the actual
 heuristics that employ the above functions.
 Most are extremely straight forward.
 */

float h_nearest_manhattan(const State &s){
    return nearest_manhattan(s.goals_remaining, s.pos);
}

float h_nearest_euclidian(const State &s){
    return nearest_flight(s.goals_remaining, s.pos);
}

// For benchmarking here are a whole host of implementations I would consider
// more or less trivial.
float h_most_trivial(const State &s) {
    return s.goals_remaining.size() != 0;
}

float h_trivial(const State &s) {
    return s.goals_remaining.size();
}

float h_less_trivial(const State &s) {
    if (s.goals_remaining.empty())
        return 0;
    return h_trivial(s) + nearest_manhattan(s.goals_remaining,s.pos) - 1; //-1 makes it passable for one goal.
}

// I really want to compute the min spanning path. But that would be to expensive (Hamiltonian path...)
// I could get super meta and run A* on the goal states to find efficient MSP... Using MST as heuristic.
// The relaxation is that I allow motion from any visited place not just the last visited goal.
// No inclusion means that the current position is not included in the MST. Instead it is joined by the
// min path to the full tree. This is preferable as it ensures the start state is a leaf.
float h_mst_man_no_inclusion(const State &s){
    return min_span_tree_manhattan(s.goals_remaining) + nearest_manhattan(s.goals_remaining,s.pos);
}

float heur_weight = 1.0f;
// Used for question 4. Rather than change the function parameters we will opaquely pass heur_weight
// obviously bad practice but ehh.
float h_mst_man_no_inclusion_opaque(const State &s){
    return (min_span_tree_manhattan(s.goals_remaining) + nearest_manhattan(s.goals_remaining,s.pos)) * heur_weight;
}
// Converse to no_inclusion. This is significantly slower since memozation is less efficient
// and less effective because the position may be a node which is even farther from the ideal HP.
float h_mst_man_inclusion(const State &s){
    set<point> cpy(s.goals_remaining);
    cpy.insert(s.pos);
    return min_span_tree_manhattan(cpy);
}

// A specific case of h_mst_no_inclusion. Has some different boundary cases, however it only
// is garunteed to work when the goal set lies on the corners of a single rectangle.
float h_corner_group_dist(const State &s) {
    if (s.goals_remaining.size() <= 1)
        return nearest_manhattan(s.goals_remaining,s.pos);
    return nearest_manhattan(s.goals_remaining,s.pos)+rect_group_dist(s.goals_remaining);
}

// Similar to above but harder to prove consistancy. As a result it is not recomended.
float h_corner_spoke(const State &s) {
    if (s.goals_remaining.size() <=1)
        return nearest_manhattan(s.goals_remaining,s.pos);
    return nearest_manhattan(s.goals_remaining,s.pos)+spoke_mass(s.goals_remaining);
}

// Cheap and dirty h_corner_group_dist. Assumes optimistic square.
float h_corners(const State &s){
    //calculate distance between corners.
    if (s.goals_remaining.size() <=1)
        return nearest_manhattan(s.goals_remaining,s.pos);
    set<point>::iterator it = s.goals_remaining.begin();
    point p = *it;
    it++;
    float d = 99999999;//MAX_FLOAT
    for(;it!=s.goals_remaining.end();it++){
        d = min(manhattan(*it,p),d);
    }
    // Degenerate when only one goal or maybe non-adjacent goals taken.
    // d * ... essentially represents the total distance between goals.
    return nearest_manhattan(s.goals_remaining,s.pos) + (s.goals_remaining.size()-1) * d;
}

/* PROBLEM SOLUTIONS */

vector<string> questionOne(Problem &problem)
{
	/// write your own code here
    // nearest_manhattan is marginally more efficient than h_nearest_euclidian (~1%)
    // essentially all other heuristics have provably identical performance.
    vector<point> path = runAstar(problem,&h_nearest_manhattan, problem.getGoals());
    return cardinalize(path);
}

vector<string> questionTwo(Problem &problem)
{
	/// write your own code here
    // no inclusion actually beats corner group dist by 29 expansions (~4%!)
    //vector<point> path = runAstar(problem,&h_corner_group_dist, problem.getGoals());
    vector<point> path = runAstar(problem,&h_mst_man_no_inclusion, problem.getGoals());
    return cardinalize(path);
}

vector<string> questionThree(Problem &problem)
{
	/// write your own code here
    vector<point> path = runAstar(problem,&h_mst_man_no_inclusion, problem.getGoals());
    return cardinalize(path);
}

// Rather than return one of the many paths generated, this will return a empty path.
// It stores the results into a file called q4log.out. In a human readable tabular form.
vector<string> questionFour(Problem &problem)
{
	/// write your own code here
    vector<float> w, l, e;
    cout << "running many itterations of A*. This may take a while"<<endl;
    cout << "|";
    // heur_weight is the global variable implicitly passed to no_inclusion_opaque.
    // First call should be slowest since subsequent calls get the benefit of previous memoizations.
    for (heur_weight = .0001f; heur_weight < 5.1f; heur_weight +=.1) {
        cout <<"*";
        cout.flush();
        int prev_exp = problem.getExpansionCounts();
        vector<point> path = runAstar(problem,&h_mst_man_no_inclusion_opaque, problem.getGoals());
        e.push_back(problem.getExpansionCounts()-prev_exp);
        w.push_back(heur_weight);
        l.push_back(path.size()-1);//only changes in state are a move. First pos is starting pos
    }
    cout <<"|"<<endl;
    cout <<"results table stored in q4log.out" <<endl;
    ofstream table_out("q4log.out");
    char buffer[100];
    table_out <<"    weight     length     expands" << endl;
    for (int i = 0;i < w.size();i++){
        sprintf(buffer,"%10.1f %10.0f %10.0f",w[i],l[i],e[i]);
        table_out << buffer << endl;
    }
    table_out.close();
	return  vector<string>();
}

/// Do not change codes below
vector<string> getPath(map<pair<int, int>, pair<int,int> > &parent, pair<int, int> goal)
{
	vector<string> path;
	pair<int, int> state = goal;
	int dx, dy;
	while (parent[state] != state)
	{
		dx = state.first - parent[state].first;
		dy = state.second - parent[state].second;
		if (dx>0)
			path.push_back("South");
		else if (dx<0)
			path.push_back("North");
		else if (dy>0)
			path.push_back("East");
		else
			path.push_back("West");
		state = parent[state];
	}
	reverse(path.begin(), path.end());
	return path;
}

vector<string> questionZero(Problem &problem)
{
	// A simple BFS to find the path from the start to the first goal.
	queue<pair<int, int> > q;
	map<pair<int, int>, pair<int, int> > parent;
	pair<int, int> start = problem.getStartState();
	vector<pair<int, int> > goals = problem.getGoals();
	if (goals.size() <= 0)
		return vector<string>();
	pair<int, int> goal = goals[0];
	q.push(start);
	parent[start] = start;
	while (!q.empty())
	{
		pair<int, int> thisState=q.front();
		q.pop();
		vector<pair<int, int> > successors = problem.getSuccessors(thisState);
		for(int i=0; i<successors.size(); ++i)
		{
			if (parent.count(successors[i]) == 0)
			{
				q.push(successors[i]);
				parent[successors[i]] = thisState;	
			}
		}
		if (parent.count(goal) != 0)
		{
			return getPath(parent, goal);
		}
	}
	return vector<string>();
}

void error()
{
	cout <<"run \'proj1 layout_name question_number\'" <<endl;
}

int main(int argc, char**argv)
{
	if (argc<3)	
	{
		error();
		return 0;
	}
	vector<string> _board;
	_board.clear();
	string namePattern = argv[1];
	string inputName; 
#ifdef _WIN32
	inputName = "layouts\\" + namePattern + ".lay";
#else
	inputName = "layouts/" + namePattern + ".lay";
#endif
	string outputName = namePattern + ".out";
	string queryName = namePattern + "_stats.out";
	try {
		ifstream fin;
		fin.open(inputName.c_str());
		while (!fin.eof())
		{
			string str;
			getline(fin, str);
			if (!fin.eof())
				_board.push_back(str);
		}
		fin.close();
	} catch (...) {
		cout << "Error while loading the layout file..." << endl;
		return 1;
	}
	Problem problem(_board);
	vector<string> _path;
	switch (argv[2][0]){
		case '1': _path = questionOne(problem); break;
		case '2': _path = questionTwo(problem); break;
		case '3': _path = questionThree(problem); break;
		case '4': _path = questionFour(problem); break;
		default: _path = questionZero(problem);
	}
	try {
		ofstream fout;
		fout.open(outputName.c_str());
		for(int i=0; i<_path.size(); ++i)
		{
			fout << _path[i] << endl;
		}
		fout.close();
	} catch (...){
		cout << "Error while saving the results..." << endl;
		return 1;
	}
	cout << "Number of expanded states: " << problem.getExpansionCounts() << endl;
	cout << "Results are saved in " << outputName << endl; 
	problem.dumpQueries(queryName);
	return 0;
}
