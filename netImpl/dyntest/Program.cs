using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace dyntest
{
    class Program
    {
        static void Main(string[] args)
        {
            dynamic a = new List<int>() { 1, 2, 3, 4 };
            dynamic c = 2;
            dynamic b = a.Count;
            Console.WriteLine(b);
        }
    }
}
