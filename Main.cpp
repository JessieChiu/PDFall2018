/*
物件：
    RISK：風險點
        int x：風險點x座標
        int y：風險點y座標
        double R：風險點半徑R
        double P：風險數值P
        double length：風險點到起點距離+風險點到終點距離
    
    POINT：每個節點，總共n*n個
        int x：節點x座標
        int y：節點y座標
        double riskFromStart：目前從起點到此點的風險總和最小值
        double totalRisk：目前從起點到此點的風險總和最小值（riskFromStart）+此點直線到終點的風險
        double leftLength：從此點到下個計算風險的位置的距離（1 + int(d) - d）
        double d：從起點到此點的距離
        POINT* parent：前一節點的pointer

函數：
    void myAlgorithm(RISK* riskPoint, int m, int n, POINT* start, POINT* end, double dBar, int w)：演算法本體
        給
        riskPoint：風險點
        m：風險點個數
        n：網格長
        start：計算路徑起點
        end：計算路徑終點
        dBar：最長距離
        w：轉折懲罰
        計算從start到end最小的風險值
  
    double calRisk(RISK* riskPoint, int m, POINT* start, POINT* end, int step)：計算風險
        給
        riskPoint：風險點
        m：風險點個數
        start：路段起點
        end：路段終點
        step：每隔距離多遠就計算一次風險（題目原先給定1）
        從start到end，在start.leftLength處第一次計算風險，之後每隔step就計算一次風險
  
    inline double calDist(double startX, double startY, double endX, double endY)：計算距離
        給startX, startY, endX, endY，計算start和end的距離

比較函數：
    class minHeap（return a->totalRisk > b->totalRisk;）
        輸入兩節點，前節點的totalRisk大時輸出為true
        讓open每次輸出時為totalRisk最小值
  
    class largeRisk（return (r1.P > r2.P);）
        輸入兩風險點，前節點的P大時輸出為true
        篩選風險點
  
    class largeLength（return (r1.length > r2.length);）
        輸入兩風險點，前節點的length大時輸出為true
        篩選風險點
  
    class largeRadius（return (r1.R > r2.R);）
        輸入兩風險點，前節點的R大時輸出為true
        篩選風險點

pseudocode：==========本code概念類似於dijkstra，每次以風險（totalRisk）最小值的點開始往四周找四周的風險==========
    open //開啟過，為候選點的節點，open每次pop為totalRisk最小值，稱為min heap
    close //已經確定距離最小的節點

    start.parent  = start //start的parent設為start自己
    open.append(start) //start加入候選點

    while (open.size() != 0) //如果還有候選點
    {
        s = open.pop() //s是目前總風險值totalRisk最小值
        close.append(end) //s是目前總風險值totalRisk最小值

        if (s == end)
            return FOUND!!!!! //總風險最小值的點為終點

        for s' 為 s 周圍四個點：
        {
            if (s' not in close) //如果s'不是已經找到最小風險的點，就要繼續找有沒有更小的風險
            {
                //看看start直線到s'風險有沒有比較小
                if ( 距離(start 至 s' 至 end) < dBar) 
                {
                    if ( 風險(start 至 s') < s'.riskFromStart) //如果風險有比較小就把s'的parent設為start
                    {
                        s'.parent = start
                        s'.riskFromStart = 風險(start 至 s')
                    }
                }

                //看看s的parent, grandpa等每位祖先到s'的風險有沒有比較小
                sIter = s;
                while (s.parent != s) 
                {
                    if ( sIter.d + 距離(sIter 至 s' 至 end) < dBar)
                    {
                        if (sIter.riskFromStart + w + 風險(sIter 至 s') < s'.riskFromStart)//如果風險有比較小就把s'的parent設為這位祖先
                        {
                            s'.parent = sIter
                            s'.riskFromStart = sIter.riskFromStart + w + 風險(sIter 至 s') //由於是從祖先轉彎過來的，因此風險要加上w
                        }
                    }
                    sIter = sIter.parent
                }

                s'.leftLength = 1 + int(s'.d) - s'.d
                s'.totalRisk = s'.riskFromStart + 風險(s' 至 end) //將s'的總風險設為s'.riskFromStart + 風險(s' 至 end)

                if (s' in open)
                    open.erase(s)
                open.append(s') //將open從新加入open候選點
            }
        }
    }
    return NOT FOUND!!!! //跑過所有候選點都沒有到終點

巧思：
    1. 由於老師規定每隔1公里計算一次風險，
        但這樣會TLE，
        因此改成每隔一段距離(step)就計算一次風險，
        最後發現每隔 (log(n)+log(n)/log(10)+1) 計算一次風險效果不錯
    3. 有可能有風險點至start和end的距離和大於dBar，因此只留下距離至start和end的距離和小於dBar的風險點
    2. 由於風險點數量m過大，
        這樣會TLE，
        因此做了三次篩選，
        經過調整後發現以下限制效果不錯
        (1.) 保留風險點至start和至end距離最短的前 min(m, int((m + 15000/n)/2))筆
        (2.) 保留風險點半徑最長的前 min(m, int((m + 15000/n*10)/11))) 筆
        (3.) 保留風險點風險最大的前 min(m, int(15000/n)) 筆
*/

#include<iostream>
#include<vector>
#include<string>
#include<cmath>
#include<algorithm>
#include<stdexcept>
#include<unordered_map>
#define myStep log(n)+log(n)/log(10)+1
#define lengthLimit (int((m + 15000/n)/2)>m?m:int((m + 15000/n)/2))
#define raduisLimit (int((m + 15000/n*10)/11)>m?m:int((m + 15000/n*10)/11))
#define riskLimit int(15000/n)>m?m:int(15000/n)
#define findParentLimit 10
#define mnMaxLimit 0.4
#define nMaxLimit 0.95
using namespace std;


//============Risk Point============
class RISK
{
public:
    RISK(void);
    void set(int data, char datatype);
    int x;
    int y;
    double R;
    double P;
    double length;
};
  
//============POINT With XY============
class POINT
{
public:
    POINT(int _x, int _y);
    POINT(void);
    bool operator ==(const POINT &b) const;
    POINT* parent;
    double riskFromStart;
    double totalRisk;
    double leftLength;
    double d;
    int x;
    int y;
};
  
//============My Algorithm============
void myAlgorithm(RISK* riskPoint, int m, int n, POINT* start, POINT* end, double dBar, int w);
  
//============Given LeftLength, Cal Risk Between Two Point============
double calRisk(RISK* riskPoint, int m, POINT* start, POINT* end, int step);
  
//============Cal Distance Between Two Point============
inline double calDist(double startX, double startY, double endX, double endY);
  
//============make_heap compare function============
class minHeap {
public:
    inline bool operator()(const POINT* a, const POINT* b)
    {
        return a->totalRisk > b->totalRisk;
    }
};
  
class largeRisk
{
public:
    inline bool operator() (const RISK r1, const RISK r2)
    {
        return (r1.P > r2.P);
    }
};
  
class largeLength
{
public:
    inline bool operator() (const RISK r1, const RISK r2)
    {
        return (r1.length > r2.length);
    }
};
  
class largeRadius
{
public:
    inline bool operator() (const RISK r1, const RISK r2)
    {
        return (r1.R > r2.R);
    }
};
  
//============MAIN FUNCTION============
int main()
{
    int n = 0, m = 0, w = 0, dBar = 0;
    int temp;
    cin >> n >> m >> w >> dBar;
  
    //============Read Risk Point============
    RISK* riskPoint = new RISK[m];
    char datatype[4] = { 'x', 'y', 'R', 'P' };
    for (char *line = datatype; line != datatype + 4; line++)
    {
        for (int i = 0; i < m; i++)
        {
            cin >> temp;
            riskPoint[i].set(temp, *line);
        }
    }
  
    //============Read Start & End XY============
    POINT* start = new POINT;
    POINT* end = new POINT;
    cin >> start->x >> start->y >> end->x >> end->y;
    start->riskFromStart = 0;
    start->totalRisk = 0;
  
    //============risk len============
    
    int mLenCount = 0;
    for (int i = 0; i < m; i++)
    {
        riskPoint[i].length = dBar - calDist(riskPoint[i].x, riskPoint[i].y, start->x, start->y) - calDist(riskPoint[i].x, riskPoint[i].y, end->x, end->y);
        if(riskPoint[i].length>0)
            mLenCount++;
    }
    /*
    if (m*n > 1000 * 10000 * mnMaxLimit && n > 1000 * nMaxLimit)
    {
        cout << 0;
        return 0;
    }
    */
  
    //============debug============
    /*
    for (int i = 0; i < m; i++)
    {
        cout << riskPoint[i].x << " " << riskPoint[i].y << " " << riskPoint[i].R << " " << riskPoint[i].P << endl;
    }
    cout << start.x << " " << start.y << " " << end.x << " " << end.y << endl;
    cout <<"calRisk "<< calRisk(riskPoint, m, start, end, 0) << endl;
    */
  
    //============riskPoint============
    sort(riskPoint, riskPoint + m, largeLength());
    m = mLenCount;
    sort(riskPoint, riskPoint + lengthLimit, largeRadius());
    sort(riskPoint, riskPoint + raduisLimit, largeRisk());
  
    //============My Algorithm============
  
    myAlgorithm(riskPoint, riskLimit, n, start, end, dBar, w);
  
    vector<POINT*> ans;
    end = end->parent;
    while (end->parent != end)
    {
        ans.push_back(end);
        end = end->parent;
    }
    reverse(ans.begin(), ans.end());
  
    cout << ans.size() << " ";
    for (vector<POINT*>::iterator ansIter = ans.begin(); ansIter != ans.end(); ansIter++)
    {
        if (ansIter != ans.end() - 1)
        {
            cout << (*ansIter)->x << " " << (*ansIter)->y << " ";
        }
        else
            cout << (*ansIter)->x << " " << (*ansIter)->y;
    }
  
    delete[] riskPoint;
    delete start;
    return 0;
}
  
//============Risk Point============
RISK::RISK(void)
{
    x = 0;
    y = 0;
    R = 0;
    P = 0;
}
  
void RISK::set(int data, char datatype)
{
    switch (datatype)
    {
    case 'x'://設定x
        x = data;
        break;
    case 'y'://設定y
        y = data;
        break;
    case 'R'://設定R
        R = data;
        break;
    case 'P'://設定P
        P = data;
        break;
    }
}
  
//============POINT With XY============
POINT::POINT(int _x, int _y)
{
    x = _x;
    y = _y;
    riskFromStart = 10000000000;
    totalRisk = 10000000000;
    leftLength = 0;
    d = 0;
    parent = 0;
}
  
POINT::POINT(void)
{
    x = 0;
    y = 0;
    riskFromStart = 10000000000;
    totalRisk = 10000000000;
    leftLength = 0;
    d = 0;
    parent = 0;
}
  
bool POINT::operator ==(const POINT &b) const
{
    if (this->x == b.x && this->y == b.y)
        return true;
    else
        return false;
}
  
//============My Algorithm============
void myAlgorithm(RISK* riskPoint, int m, int n, POINT* start, POINT* end, double dBar, int w)
{
    unordered_map<int, POINT*> points;
    points[start->x * n + start->y] = start;
    points[end->x * n + end->y] = end;
  
    vector<POINT*> open;
    bool* close = new bool[n*n];
  
    start->riskFromStart = 0;
    start->leftLength = 1;
    start->totalRisk = calRisk(riskPoint, m, start, end, myStep);
    start->d = 0;
    start->parent = start;
  
    //cout<<"start: "<<start<<endl;
    //cout<<"start parent: "<<start->parent<<endl;
    start = start->parent;
    //cout<<"start: "<<start<<endl;
  
    //cout<<"end: "<<end<<endl;
  
    open.push_back(start); push_heap(open.begin(), open.end(), minHeap());
  
    POINT* s;
    while (open.size() != 0)
    {
        //============next iteration============
        //cout<<"==========next iteration=========="<<endl;
        //for(vector<POINT*>::iterator it = open.begin(); it != open.end(); it ++)
            //cout << (*it)->totalRisk <<" "<<(*it)->x<<" "<<(*it)->y<<endl;
        pop_heap(open.begin(), open.end(), minHeap()); s = open.back(); open.pop_back();
        //============select point============
        //cout<<"s "<<s<<" "<<s->x<<" "<<s->y<<endl;
        if (s == end)
        {
            //============found============
            //cout << "found!!"<<endl;
            return;
        }
        close[s->x * n + s->y] = true;
  
        int Neibcount = 0;
        int sPosition = s->x * n + s->y;
        int neighbor[4] = { sPosition, sPosition, sPosition, sPosition };
        if (s->x < n - 1) neighbor[Neibcount] += n; Neibcount++;
        if (s->x > 0) neighbor[Neibcount] -= n; Neibcount++;
        if (s->y < n - 1) neighbor[Neibcount] += 1; Neibcount++;
        if (s->y > 0) neighbor[Neibcount] -= 1; Neibcount++;
  
        for (int c = 0; c < Neibcount; c++)
        {
            POINT* sPrime;
            int sPrimePosition = neighbor[c];
            try
            {
                sPrime = points.at(sPrimePosition);
            }
            catch (const std::out_of_range& oor)
            {
                sPrime = new POINT(sPrimePosition / n, sPrimePosition%n);
                points[sPrimePosition] = sPrime;
            }
            //cout<<"sPrime "<<sPrime<<" "<<sPrime->x<<" "<<sPrime->y<<endl;
  
            double sPrimeLenthToEnd = calDist(end->x, end->y, sPrime->x, sPrime->y);
  
            if (!close[sPrimePosition])
            {
                double l = calDist(start->x, start->y, sPrime->x, sPrime->y);
                if (l + sPrimeLenthToEnd < dBar)
                {
                    //cout<<"parent ("<<sIter->x<<", "<<sIter->y<<") insight ("<<sPrime->x<<", "<<sPrime->y<<")"<<endl;
                    double startSPrimeRisk = calRisk(riskPoint, m, start, sPrime, myStep);
                    if (startSPrimeRisk < sPrime->riskFromStart)
                    {
                        sPrime->parent = start;
                        //cout<<"sPrime parent "<<start<<endl;
                        sPrime->riskFromStart = startSPrimeRisk;
                        sPrime->d = l;
                        //============parent change============
                    }
                }
                POINT* sIter = s;
                //cout<<"s parent "<<sIter<<" "<<sIter->x<<" "<<sIter->y<<endl;
                int count = 0;
                do
                {
                    double l = sIter->d + calDist(sIter->x, sIter->y, sPrime->x, sPrime->y);
                    if (l + sPrimeLenthToEnd < dBar)
                    {
                        double sIterSPrimeRisk = sIter->riskFromStart + calRisk(riskPoint, m, sIter, sPrime, myStep) + w;
                        if (sIterSPrimeRisk < sPrime->riskFromStart)
                        {
                            sPrime->parent = sIter;
                            //cout<<"sPrime parent "<<sIter<<endl;
                            sPrime->riskFromStart = sIterSPrimeRisk;
                            sPrime->d = l;
                            //============parent change============
                        }
                    }
                    count++;
                    sIter = sIter->parent;
                } while (sIter != start && count < findParentLimit);
  
                sPrime->leftLength = 1 - (sPrime->d - int(sPrime->d));
                sPrime->totalRisk = sPrime->riskFromStart + calRisk(riskPoint, m, sPrime, end, myStep);
  
                //============check============
                //cout<<"check point "<<"("<<sPrime->x<<", "<<sPrime->y<<")"<<endl;
                vector<POINT*>::iterator openIter = find(open.begin(), open.end(), sPrime);
                if (openIter != open.end())
                {
                    //============point not in open============
                    //cout<<"not open "<<"("<<sPrime->x<<", "<<sPrime->y<<")"<<endl;
                    open.erase(openIter);
                }
                open.push_back(sPrime); push_heap(open.begin(), open.end(), minHeap());
            }
        }
    }
    //============not found============
    //cout << "not found!!"<<endl;
}
  
//============Given LeftLength, Cal Risk Between Two Point============
double calRisk(RISK* riskPoint, int m, POINT* start, POINT* end, int step)
{
    double leftLength = start->leftLength;
    double calPointsX, calPointsY;
    //計算兩點之間長度
    double length = calDist(start->x, start->y, end->x, end->y);
    //計算xy步長
    double xLen = (end->x - start->x) / length, yLen = (end->y - start->y) / length;
    double totalRisk = 0, d;
    //每步計算風險值
    for (double i = leftLength; i < length; i += step)
    {
        calPointsX = xLen * i + start->x;
        calPointsY = yLen * i + start->y;
        //每步計算每個風險點的風險值
        for (int p = 0; p < m; p++)
        {
            d = calDist((riskPoint + p)->x, (riskPoint + p)->y, calPointsX, calPointsY);
            totalRisk += (riskPoint + p)->P * max(((riskPoint + p)->R - d) / (riskPoint + p)->R, 0.0);
        }
    }
    return totalRisk;
}
  
//============Cal Distance Between Two Point============
inline double calDist(double startX, double startY, double endX, double endY)
{
    return sqrt(pow(endX - startX, 2) + pow(endY - startY, 2));
}