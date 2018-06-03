using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml;


namespace GraphOpenStreetMap
{
    delegate double Heuristic(double x1, double y1, double x2, double y2);

    class Deq<T>
    {
        T[] array;

        public Deq()
        {
            array = new T[0];
        }
        public int Count
        {
            get
            {
                return array.Length;
            }
        }
        public bool Empty
        {
            get
            {
                return array.Length > 0;
            }
        }
        public void PushBack(T item)
        {
            Array.Resize(ref array, array.Length + 1);
            array[array.Length - 1] = item;
        }
        public void PushFront(T item)
        {
            Array.Resize(ref array, array.Length + 1);
            for (int i = array.Length - 1; i > 0; i--)
                array[i] = array[i - 1];
            array[0] = item;
        }
        public T PopBack()
        {
            T item = array[array.Length - 1];
            Array.Resize(ref array, array.Length - 1);
            return item;
        }
        public T PopFront()
        {
            T item = array[0];
            for (int i = 0; i < array.Length - 1; i++)
                array[i] = array[i + 1];
            Array.Resize(ref array, array.Length - 1);
            return item;
        }
        public T Front
        {
            get
            {
                return array[0];
            }
        }
        public T Back
        {
            get
            {
                return array[array.Length - 1];
            }
        }
    }


    class Program
    {

        private static readonly double major = 6378137.0;
        private static readonly double minor = 6356752.3142;
        private static readonly double ratio = minor / major;
        private static readonly double e = Math.Sqrt(1.0 - (ratio * ratio));
        private static readonly double com = 0.5 * e;
        private static readonly double degToRad = Math.PI / 180.0;

        struct coord
        {
            public double lat;
            public double lon;
        }

        struct pointCom
        {
            public long id;
            public bool isVisited;
            public long son;
        }

        struct pointBord
        {
            public long id;
            public bool isVisited_i;
            public bool isVisited_j;
            public long son;
        }

        struct pointDijk
        {
            public long id;
            public double x;
            public double y;
            public double weight;
            public long parent;
            public bool isVisited;
        }

        struct pointLevit
        {
            public int M;
            public long id;
            public double x;
            public double y;
            public double weight;
            public double f;
            public long parent;
        }

        struct pointA
        {
            public long id;
            public double x;
            public double y;
            public double weight;
            public double f;
            public long parent;
            public bool isVisited;
            public bool isInQ;
        }

        static double Euclid(double x1, double y1, double x2, double y2)
        {
            return Math.Sqrt(Math.Pow(x2 - x1, 2.0) + Math.Pow(y2 - y1, 2.0));
        }

        static double Manhattan(double x1, double y1, double x2, double y2)
        {
            return (Math.Abs(x1 - x2) + Math.Abs(y1 - y2));
        }

        static double Chebyshev(double x1, double y1, double x2, double y2)
        {
            return Math.Max(Math.Abs(x1 - x2), Math.Abs(y1 - y1));
        }

        private static double minlon;
        private static double maxlon;
        private static double minlat;
        private static double maxlat;

        private static SortedDictionary<long, coord> Nodes = new SortedDictionary<long, coord>();
        private static SortedDictionary<long, List<long>> AddjestedList = new SortedDictionary<long, List<long>>();
        private static List<string> Valid = new List<string>() {
            "motorway", "motorway_link", "trunk", "trunk_link", "primary", "primary_link", "secondary",
                "secondary_link", "tertiary", "tertiary_link", "unclassified", "road", "service", "living_street", "residential"
        };


        private static List<long>[] DijkstraRoute = new List<long>[10];
        private static List<long>[] LevitRoute = new List<long>[10];
        private static List<long>[] ARoute = new List<long>[11];
        private static pointDijk[] DijkstranPoint;
        private static pointLevit[] LevitPoint;
        private static pointA[] APoint;
        private static List<long> idFinalPoints = new List<long>();

        static void Osm(string path)
        {

            XmlDocument xDoc = new XmlDocument();
            xDoc.Load(path);
            XmlElement xRoot = xDoc.DocumentElement;
            XmlNodeList nodes = xRoot.SelectNodes("node");
            maxlat = double.Parse(xRoot.SelectSingleNode("bounds").Attributes["maxlat"].Value, CultureInfo.InvariantCulture);
            minlon = double.Parse(xRoot.SelectSingleNode("bounds").Attributes["minlon"].Value, CultureInfo.InvariantCulture);
            maxlon = double.Parse(xRoot.SelectSingleNode("bounds").Attributes["maxlon"].Value, CultureInfo.InvariantCulture);
            minlat = double.Parse(xRoot.SelectSingleNode("bounds").Attributes["minlat"].Value, CultureInfo.InvariantCulture);
            foreach (XmlNode n in nodes)
            {
                long id = long.Parse(n.SelectSingleNode("@id").Value);
                double lat = double.Parse(n.SelectSingleNode("@lat").Value, CultureInfo.InvariantCulture);
                double lon = double.Parse(n.SelectSingleNode("@lon").Value, CultureInfo.InvariantCulture);
                coord Node_coord;
                Node_coord.lat = lat;
                Node_coord.lon = lon;
                Nodes.Add(id, Node_coord);
            }
            Valid.Sort();
            XmlNodeList ways = xRoot.SelectNodes("//way[.//tag[@k = 'highway']]");
            foreach (XmlNode n in ways)
            {
                string validway = n.SelectSingleNode("tag[@k = 'highway']").Attributes["v"].Value;
                if (Valid.BinarySearch(validway) >= 0)
                {
                    XmlNodeList nd = n.SelectNodes("nd");
                    List<long> nodes_list_id = new List<long>();
                    foreach (XmlNode m in nd)
                    {
                        long id = long.Parse(m.SelectSingleNode("@ref").Value);
                        nodes_list_id.Add(id);
                    }
                    for (int i = 0; i < nodes_list_id.Count(); ++i)
                    {
                        if (i < nodes_list_id.Count() - 1)
                        {
                            if (AddjestedList.ContainsKey(nodes_list_id[i]))
                            {
                                AddjestedList[nodes_list_id[i]].Add(nodes_list_id[i + 1]);
                            }
                            else
                            {
                                AddjestedList.Add(nodes_list_id[i], new List<long>());
                                AddjestedList[nodes_list_id[i]].Add(nodes_list_id[i + 1]);
                            }
                        }
                        if (i >= 1)
                        {
                            if (AddjestedList.ContainsKey(nodes_list_id[i]))
                            {
                                AddjestedList[nodes_list_id[i]].Add(nodes_list_id[i - 1]);
                            }
                            else
                            {
                                AddjestedList.Add(nodes_list_id[i], new List<long>());
                                AddjestedList[nodes_list_id[i]].Add(nodes_list_id[i - 1]);
                            }
                        }
                    }
                }
            }
            XmlNodeList finalPoints = xRoot.SelectNodes("//node[.//tag[@k = 'amenity']]");
            int count = 0;
            foreach (XmlNode n in finalPoints)
            {
                string type = n.SelectSingleNode("tag[@k = 'amenity']").Attributes["v"].Value;
                if (type == "hospital")
                {
                    double lat = double.Parse(n.SelectSingleNode("@lat").Value, CultureInfo.InvariantCulture);
                    double lon = double.Parse(n.SelectSingleNode("@lon").Value, CultureInfo.InvariantCulture);
                    long id = NearPoint(lat, lon);
                    idFinalPoints.Add(id);
                    count++;
                }
                if (count > 9)
                    break;
                else
                {
                    if (type == "police")
                    {
                        double lat = double.Parse(n.SelectSingleNode("@lat").Value, CultureInfo.InvariantCulture);
                        double lon = double.Parse(n.SelectSingleNode("@lon").Value, CultureInfo.InvariantCulture);
                        long id = NearPoint(lat, lon);
                        idFinalPoints.Add(id);
                        count++;
                    }
                }
            }
        }


        private static double DegToRad(double deg)
        {
            return deg * degToRad;
        }

        public static double lonToX(double lon)
        {
            return major * DegToRad(lon) * 0.1;
        }

        public static double latToY(double lat)
        {
            lat = Math.Min(89.5, Math.Max(lat, -89.5));
            double phi = DegToRad(lat);
            double sinphi = Math.Sin(phi);
            double con = e * sinphi;
            con = Math.Pow(((1.0 - con) / (1.0 + con)), com);
            double ts = Math.Tan(0.5 * ((Math.PI * 0.5) - phi)) / con;
            return 0 - major * Math.Log(ts) * 0.1;
        }

        private static List<double> FinalWeigth = new List<double>();

        static double AStarWeight(long begin_node, long end_node, Heuristic h)
        {
            List<pointA> Q = new List<pointA>();
            ICollection<long> keys = AddjestedList.Keys;
            APoint = new pointA[keys.Count];
            int k = 0;
            double end_x, end_y;
            end_x = lonToX(Nodes[end_node].lon);
            end_y = latToY(Nodes[end_node].lat);
            APoint[k].id = begin_node;
            APoint[k].x = lonToX(Nodes[begin_node].lon);
            APoint[k].y = latToY(Nodes[begin_node].lat);
            APoint[k].weight = 0;
            APoint[k].parent = 0;
            APoint[k].isVisited = false;
            APoint[k].isInQ = true;
            APoint[k].f = APoint[k].weight + h(APoint[k].x, APoint[k].y, end_x, end_y);
            Q.Add(APoint[k]);
            k++;
            foreach (long i in keys)
            {
                if (i != begin_node)
                {
                    APoint[k].id = i;
                    APoint[k].x = lonToX(Nodes[i].lon);
                    APoint[k].y = latToY(Nodes[i].lat);
                    APoint[k].weight = Double.PositiveInfinity;
                    APoint[k].parent = 0;
                    APoint[k].isVisited = false;
                    APoint[k].isInQ = false;
                    APoint[k].f = 0;
                    k++;
                }
            }
            while (Q.Count != 0)
            {
                double minF = Double.PositiveInfinity;
                long minKey = 0;
                int index_inQ = 0;
                int index_minKey = 0;
                for (int i = 0; i < Q.Count; ++i)
                {
                    if (Q[i].f < minF)
                    {
                        minF = Q[i].f;
                        minKey = Q[i].id;
                        index_inQ = i;  //индекс в очереди, не в массиве
                    }
                }
                if (minKey == end_node)
                    break;
                for (int i = 0; i < keys.Count; ++i)
                {
                    if (APoint[i].id == minKey)
                    {
                        index_minKey = i;
                        break;
                    }
                }
                Q.RemoveAt(index_inQ);
                APoint[index_minKey].isInQ = false;
                APoint[index_minKey].isVisited = true;
                for (int i = 0; i < AddjestedList[minKey].Count(); ++i)
                {
                    long neighbourPoint = AddjestedList[minKey][i];
                    int index_neighbour = 0;
                    for (int p = 1; p < keys.Count; ++p)
                    {
                        if (APoint[p].id == neighbourPoint)
                        {
                            index_neighbour = p;
                            break;
                        }
                    }
                    double weightCurrEdge = Math.Sqrt(Math.Pow(APoint[index_minKey].x - APoint[index_neighbour].x, 2.0) + Math.Pow(APoint[index_minKey].y - APoint[index_neighbour].y, 2.0));
                    if (APoint[index_neighbour].isVisited && APoint[index_neighbour].weight <= APoint[index_minKey].weight + weightCurrEdge)
                        continue;
                    if (!APoint[index_neighbour].isVisited || APoint[index_neighbour].weight > APoint[index_minKey].weight + weightCurrEdge)
                    {
                        APoint[index_neighbour].weight = APoint[index_minKey].weight + weightCurrEdge;
                        APoint[index_neighbour].parent = index_minKey;
                        APoint[index_neighbour].f = APoint[index_neighbour].weight + h(APoint[index_neighbour].x, APoint[index_neighbour].y, end_x, end_y);
                        if (!APoint[index_neighbour].isInQ)
                        {
                            Q.Add(APoint[index_neighbour]);
                            APoint[index_neighbour].isInQ = true;
                        }
                    }
                }
            }

            //ARoute[way] = new List<long>();
            for (int i = 0; i < keys.Count; ++i)
            {
                if (APoint[i].id == end_node)
                {
                    return APoint[i].weight;
                }
                else return 0;
            }
            return 0;
        }

        static double FindARoute(int numbRoute, long endPoint, int N)
        {
            long index_endPoint = -1;
            double weight = -1;
            for (int i = 0; i < N; ++i)
                if (APoint[i].id == endPoint)
                {
                    index_endPoint = i;
                    weight = APoint[i].weight;
                    break;
                }
            if (index_endPoint == -1)
            {
                Console.WriteLine("No way to the {0} point!", numbRoute);
                return 0;
            }
            while (index_endPoint != 0)
            {
                ARoute[numbRoute].Add(APoint[index_endPoint].id);
                index_endPoint = APoint[index_endPoint].parent;
            }
            ARoute[numbRoute].Add(APoint[index_endPoint].id);

            
            return weight;
        }

        static void AStar(long begin_node, long end_node, Heuristic h, int way)
        {
            List<pointA> Q = new List<pointA>();
            ICollection<long> keys = AddjestedList.Keys;
            APoint = new pointA[keys.Count];
            int k = 0;
            double end_x, end_y;
            end_x = lonToX(Nodes[end_node].lon);
            end_y = latToY(Nodes[end_node].lat);
            APoint[k].id = begin_node;
            APoint[k].x = lonToX(Nodes[begin_node].lon);
            APoint[k].y = latToY(Nodes[begin_node].lat);
            APoint[k].weight = 0;
            APoint[k].parent = 0;
            APoint[k].isVisited = false;
            APoint[k].isInQ = true;
            APoint[k].f = APoint[k].weight + h(APoint[k].x, APoint[k].y, end_x, end_y);
            Q.Add(APoint[k]);
            k++;
            foreach (long i in keys)
            {
                if (i != begin_node)
                {
                    APoint[k].id = i;
                    APoint[k].x = lonToX(Nodes[i].lon);
                    APoint[k].y = latToY(Nodes[i].lat);
                    APoint[k].weight = Double.PositiveInfinity;
                    APoint[k].parent = 0;
                    APoint[k].isVisited = false;
                    APoint[k].isInQ = false;
                    APoint[k].f = 0;
                    k++;
                }
            }
            while (Q.Count != 0)
            {
                double minF = Double.PositiveInfinity;
                long minKey = 0;
                int index_inQ = 0;
                int index_minKey = 0;
                for (int i = 0; i < Q.Count; ++i)
                {
                    if (Q[i].f < minF)
                    {
                        minF = Q[i].f;
                        minKey = Q[i].id;
                        index_inQ = i;  //индекс в очереди, не в массиве
                    }
                }
                if (minKey == end_node)
                    break;
                for (int i = 0; i < keys.Count; ++i)
                {
                    if (APoint[i].id == minKey)
                    {
                        index_minKey = i;
                        break;
                    }
                }
                Q.RemoveAt(index_inQ);
                APoint[index_minKey].isInQ = false;
                APoint[index_minKey].isVisited = true;
                for (int i = 0; i < AddjestedList[minKey].Count(); ++i)
                {
                    long neighbourPoint = AddjestedList[minKey][i];
                    int index_neighbour = 0;
                    for (int p = 1; p < keys.Count; ++p)
                    {
                        if (APoint[p].id == neighbourPoint)
                        {
                            index_neighbour = p;
                            break;
                        }
                    }
                    double weightCurrEdge = Math.Sqrt(Math.Pow(APoint[index_minKey].x - APoint[index_neighbour].x, 2.0) + Math.Pow(APoint[index_minKey].y - APoint[index_neighbour].y, 2.0));
                    if (APoint[index_neighbour].isVisited && APoint[index_neighbour].weight <= APoint[index_minKey].weight + weightCurrEdge)
                        continue;
                    if (!APoint[index_neighbour].isVisited || APoint[index_neighbour].weight > APoint[index_minKey].weight + weightCurrEdge)
                    {
                        APoint[index_neighbour].weight = APoint[index_minKey].weight + weightCurrEdge;
                        APoint[index_neighbour].parent = index_minKey;
                        APoint[index_neighbour].f = APoint[index_neighbour].weight + h(APoint[index_neighbour].x, APoint[index_neighbour].y, end_x, end_y);
                        if (!APoint[index_neighbour].isInQ)
                        {
                            Q.Add(APoint[index_neighbour]);
                            APoint[index_neighbour].isInQ = true;
                        }
                    }
                }
            }

            ARoute[way] = new List<long>();
            FinalWeigth.Add(FindARoute(way, end_node, keys.Count));
        }

        private static pointCom[] ComPoint;

        static void Neighbour(long begin_node)
        {
            ComPoint = new pointCom[11];
            ComPoint[0].id = begin_node;
            ComPoint[0].isVisited = true;
            ComPoint[0].son = 0;
            for(int i = 1; i<11; ++i)
            {
                ComPoint[i].id = idFinalPoints[i-1];
                ComPoint[i].isVisited = false;
                ComPoint[i].son = 0;
            }
            long last_point = 0;
            for(int k = 0; k<10; ++k)
            {
                double minWeight = Double.PositiveInfinity;
                int minPoint = -1;
                for (int i = 1; i<11; ++i)
                {
                    if(!ComPoint[i].isVisited)
                    {
                        double weight = AStarWeight(ComPoint[last_point].id, ComPoint[i].id, Manhattan);
                        if (minWeight>weight)
                        {
                            minWeight = weight;
                            minPoint = i;
                        }
                    }
                }
                ComPoint[minPoint].isVisited = true;
                ComPoint[last_point].son = ComPoint[minPoint].id;
                last_point = minPoint;
            }
            ComPoint[last_point].son = ComPoint[0].id;

        }

        private static pointBord[] BordPoint;

        static void Border(long begin_node)
        {
            BordPoint = new pointBord[11];
            BordPoint[0].id = begin_node;
            BordPoint[0].isVisited_i = false;
            BordPoint[0].isVisited_j = false;
            BordPoint[0].son = 0;
            for (int i = 1; i < 11; ++i)
            {
                BordPoint[i].id = idFinalPoints[i - 1];
                BordPoint[i].isVisited_i = false;
                BordPoint[i].isVisited_j = false;
                BordPoint[i].son = 0;
            }
            double[,] BorderArr = new double[11, 11];
            for(int i = 0; i<11; ++i)
            {
                for(int j = 0; j<11; ++j)
                {
                    if (i == j)
                        BorderArr[i, j] = Double.PositiveInfinity;
                    else
                    {
                        BorderArr[i, j] = AStarWeight(BordPoint[i].id,BordPoint[j].id,Manhattan);
                    }
                }
            }
            double[] minI = new double[11];
            double[] minJ = new double[11];
            for (int m = 0; m<11; ++m)
            {

                for (int i = 0; i < 11; ++i)
                {
                    minI[i] = Double.PositiveInfinity;
                    minJ[i] = Double.PositiveInfinity;
                }
                for (int i = 0; i<11; ++i)
                {
                    if (!BordPoint[i].isVisited_i)
                    {
                        for (int j = 0; j < 11; ++j)
                        {
                            if (!BordPoint[i].isVisited_j)
                            {
                                if(minI[i]>BorderArr[i,j])
                                {
                                    minI[i] = BorderArr[i, j];
                                }
                            }
                        }
                        for (int j = 0; j < 11; ++j)
                        {
                            BorderArr[i,j] = BorderArr[i, j] - minI[i];
                        }
                    }
                }

            }
        }

        static void Csv()
        {
            string pathСsv;
            Console.WriteLine("Input path for csv file:");
            pathСsv = Console.ReadLine();
            System.IO.StreamWriter outputFile = new System.IO.StreamWriter(pathСsv + ".csv");
            outputFile.WriteLine("Node;Way");

            for (int i = 0; i < 10; ++i)
            {
                string line = "";
                line += idFinalPoints[i];
                line += ";";
                line += "{";
                for (int j = ARoute[i].Count() - 1; j >= 0; j--)
                {
                    line += ARoute[i][j];
                    line += ",";
                }
                line += "}";
                outputFile.WriteLine(line);
            }
            outputFile.Close();
        }

        static void Svg(long begin_node)
        {
            string pathSvg;
            Console.WriteLine("Input path for svg file:");
            pathSvg = Console.ReadLine();
            System.IO.StreamWriter outputFile = new System.IO.StreamWriter(pathSvg + ".svg");
            outputFile.WriteLine("<svg version = \"1.1\" baseProfile = \"full\" xmlns = \"http://www.w3.org/2000/svg\" >");
            string line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[begin_node].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[begin_node].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"black\" />";
            outputFile.WriteLine(line);
            ICollection<long> keys = AddjestedList.Keys;
            foreach (long i in keys)
            {
                for (int j = 0; j < AddjestedList[i].Count(); ++j)
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[i].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[AddjestedList[i][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[i].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[AddjestedList[i][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"blue\" stroke-width= \"1\" />";
                    outputFile.WriteLine(line);
                }
            }

            
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[begin_node].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[begin_node].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"black\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[0]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[0]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"gray\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"red\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[2]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[2]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"maroon\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[3]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[3]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"yellow\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[4]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[4]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"darksalmon\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[5]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[5]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"darkgoldenrod\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[6]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[6]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"gold\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[7]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[7]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"green\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[8]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[8]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"cyan\" />";
            outputFile.WriteLine(line);
            line = "<circle ";
            line += "cx=\"" + System.Convert.ToString(lonToX(Nodes[idFinalPoints[9]].lon) - lonToX(minlon)).Replace(",", ".") + "\" cy=\"" + System.Convert.ToString(-latToY(Nodes[idFinalPoints[9]].lat) + latToY(maxlat)).Replace(",", ".") + "\" r=\"20\" fill=\"blue\" />";
            outputFile.WriteLine(line);
 


            for (int j = 0; j < ARoute[1].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[1][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[1][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[1][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[1][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"grey\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[2].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[2][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[2][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[2][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[2][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"red\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[3].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[3][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[3][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[3][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[3][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"maroon\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[4].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[4][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[4][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[4][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[4][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"yellow\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[5].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[5][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[5][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[5][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[5][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"darksalmon\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[6].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[6][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[6][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[6][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[6][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"darkgoldenrod\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[7].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[7][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[7][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[7][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[7][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"gold\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[8].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[8][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[8][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[8][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[8][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"green\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[9].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[9][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[9][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[9][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[9][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"cyan\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }
            for (int j = 0; j < ARoute[10].Count() - 1; ++j)
            {
                {
                    line = "<line ";
                    line += "x1=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[10][j]].lon) - lonToX(minlon)).Replace(",", ".") + "\" x2=\"" + System.Convert.ToString(lonToX(Nodes[ARoute[10][j + 1]].lon) - lonToX(minlon)).Replace(",", ".") + "\" y1=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[10][j]].lat) + latToY(maxlat)).Replace(",", ".") + "\" y2=\"" + System.Convert.ToString(-latToY(Nodes[ARoute[10][j + 1]].lat) + latToY(maxlat)).Replace(",", ".") + "\" ";
                    line += "stroke = \"blue\" stroke-width= \"10\" />";
                    outputFile.WriteLine(line);
                }
            }

            outputFile.WriteLine("</svg>");
            outputFile.Close();
        }

        static long NearPoint(double lat, double lon)
        {
            long id = 0;
            double min = Double.PositiveInfinity;
            ICollection<long> keys = AddjestedList.Keys;
            foreach (long i in keys)
            {
                if (Manhattan(lat, lon, Nodes[i].lat, Nodes[i].lon) < min)
                {
                    id = i;
                    min = Manhattan(lat, lon, Nodes[i].lat, Nodes[i].lon);
                }
            }

            return id;
        }

        

        static void Main(string[] args)
        {
            string path;
            Console.WriteLine("Insert full way to osm file:");
            path = Console.ReadLine();
            Osm(path);
            Console.WriteLine("Inset LAT for begin point (from {0} to {1})", minlat, maxlat);
            double lat = Double.Parse(Console.ReadLine());
            Console.WriteLine("Inset LON for begin point (from {0} to {1})", minlon, maxlon);
            double lon = Double.Parse(Console.ReadLine());
            long begin_node = NearPoint(lat, lon);
            Console.WriteLine("{0}", begin_node);
            Neighbour(begin_node);
            for (int i = 0; i < 11; i++)
            {
                AStar(ComPoint[i].id, ComPoint[i].son, Manhattan, i);
            }
            double weight = 0;
            for (int i = 0; i < 11; i++)
            {
                weight += FinalWeigth[i];
            }
            Console.WriteLine("Distation {0}: ", weight*6.2/1000);
            Svg(begin_node);
            Console.ReadLine();
        }
    }
}
