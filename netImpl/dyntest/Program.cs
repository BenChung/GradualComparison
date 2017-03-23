using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace dyntest
{
    class D
    {
        public D(E f)
        {
            this.f = f;
        }
        public E f;
        public dynamic m(dynamic x)
        {
            return this.f.m(this.f);
        }

    }
    class E
    {
        public E()
        {

        }
        public E m(E x)
        {
            return x;
        }

    }
    class Program
    {
        static void Main(string[] args)
        {
            new D(new E()).m(new E());
        }
    }
}
